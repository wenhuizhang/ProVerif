(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2021                      *
 *                                                           *
 *************************************************************)

(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)
let stdout_channel = stdout

open Unix

let tmpdir = ref ""

let timeout = ref 0

let additional_options = ref []
    
let error s =
  print_string s;
  exit 2
    
type error_t =
  | InfoNotFound
  | EmptyInfo
  | UnfinishedInfo
  | TimeNotFound
  | IncorrectTime
  | IncorrectRSS
  | TimeOut
      
type time_res_t =
  | NoTime
  | Error
  | Time of float

type mode_t =
  | Test
  | TestAdd
  | Add
  | Update

type time_record =
    { mutable total : float;
      mutable user : float;
      mutable system : float }
      
external get_resources : time_record -> int = "get_resources"

(* Configuration *)

(* [find_file filename dir_list] looks for the file [filename]
   in the list of directories [dir_list].
   Raises [Not_found] if [filename] does not exist in any
   directory in [dir_list]. *)
  
let rec find_file filename = function
  | [] -> raise Not_found
  | None :: l ->
      find_file filename l
  | (Some a)::l ->
      let full_name = Filename.concat a filename in
      if Sys.file_exists full_name then
	full_name
      else
	find_file filename l
  
let exe_extension = if Sys.os_type = "Unix" then "" else ".exe"
  
let find_exe dir_list exe_name =
  let exe_name_with_extension = exe_name ^ exe_extension in
  (* First, try to find the executable in the current directory,
     then in the directories mentioned in [dir_list],
     and as a last resort, in the PATH *)
  try
    find_file exe_name_with_extension ((Some Filename.current_dir_name) :: dir_list)
  with Not_found ->
    (* as a last resort, try to find the executable in the PATH *)
    exe_name_with_extension

let home_dir_opt =
  try
    Some (Sys.getenv "HOME")
  with Not_found ->
    None
    
let cv_default_dir_opt =
  match home_dir_opt with
  | Some home_dir -> Some (Filename.concat home_dir "CryptoVerif")
  | None -> None

let pv_default_dir_opt =
  match home_dir_opt with
  | Some home_dir -> Some (Filename.concat (Filename.concat home_dir "proverif") "proverif")
  | None -> None
    
type config_t =
    { executable : string;
      expected_result_marker : string;
      is_result_line : string -> bool;
        (* [is_result_line l] is true iff [l] should be kept in the result *)
      build_option_table : string -> (string * string list) list
        (* [build_option_table dirname] returns a list of [(ext_i, options_i)]
           such that the files that end with [ext_i] should be analyzed 
           with options [options_i]. *)}

let cv_config() =
  let cv_file = find_exe [cv_default_dir_opt] "cryptoverif" in
  { executable = cv_file;
    expected_result_marker = "EXPECTED";
    is_result_line = (fun l ->
      (StringPlus.starts_with l "RESULT Could not prove") ||
      (StringPlus.starts_with l "All queries proved"));
    build_option_table = (fun dirname -> 
      let cv_options =
	let cv_lib_name = Filename.concat dirname "mylib.cvl" in
	if Sys.file_exists cv_lib_name then
	  [ "-o"; !tmpdir; "-lib" ; cv_lib_name ]
	else
	  [ "-o"; !tmpdir ]
      in
      let ocv_options =
	let cv_lib_name = Filename.concat dirname "mylib.ocvl" in
	if Sys.file_exists cv_lib_name then
	  [ "-o"; !tmpdir; "-lib" ; cv_lib_name ]
	else
	  [ "-o"; !tmpdir ]
      in
      [(".cv", cv_options); (".pcv", cv_options); (".ocv", ocv_options)])
  }      
	
let pv_config() = 
  let pv_file = find_exe [pv_default_dir_opt] "proverif" in
  let test_option = ["-test"] in
  let basic_options =
    [ (".pi", test_option); (".horn", test_option); (".horntype", test_option) ]
  in
  { executable = pv_file;
    expected_result_marker = "EXPECTPV";
    is_result_line = (fun l -> StringPlus.starts_with l "RESULT");
    build_option_table = (fun dirname ->
      let pv_lib_name = Filename.concat dirname "mylib.pvl" in
      if Sys.file_exists pv_lib_name then
	let pv_options = [ "-test" ; "-lib" ; pv_lib_name ] in
	(".pcv", pv_options) :: (".pv", pv_options) :: basic_options
      else
	try 
	  let cryptoverif_pvl =
	    find_file "cryptoverif.pvl"
	      [ Some Filename.current_dir_name; cv_default_dir_opt; pv_default_dir_opt ]
	  in
	  (".pcv", [ "-test" ; "-lib" ; cryptoverif_pvl ]) :: (".pv", test_option) :: basic_options
	with Not_found ->
	  print_string "Error: cryptoverif.pvl not found. Cannot analyze *.pcv files.\n";
	  (".pv", test_option) :: basic_options
				    )
  }      


(* [interpret_time_line errors reversed_result time_line] 
   interprets the time line [time_line] output by the xtime program.
   [reversed_result: string list] should be the result lines output by
   CryptoVerif or ProVerif, in reversed order.
   [errors: error_t list ref] is a reference to a list of errors, 
   containing errors already seen.
   It returns
   [(errors', result', time, max_rss, time_string)]
   where
   - [errors': error_t list] is a list of errors, containing those in [errors]
   plus those met inside [interpret_time_line]. 
   - [result': string list] is the result lines in the right order, including
   [time_line] when it is in fact an error message.
   - [time: time_res_t] is the total runtime of CryptoVerif or ProVerif,
   in seconds. (It is [NoTime] when it is could not be determined and
   [Error] when [time_line] was in fact an error.)
   - [max_rss: int option] is the maximum memory usage, in kb.
   (It is [None] when it could not be determined.)
   - [time_string: string] is empty when [time_line] is in fact an error 
   message ([time_line] is already included in [result'] and [time_line]
   followed by a newline otherwise. *)
    
let interpret_time_line errors reversed_result time_line =
  if StringPlus.starts_with time_line "xtime: timeout" then
    (TimeOut :: (!errors), None, NoTime, None, time_line ^"\n")
  else if StringPlus.starts_with time_line "xtime:" then
    (!errors, Some (List.rev (time_line :: reversed_result)), Error, None, "")
  else if StringPlus.contains time_line "user" && StringPlus.contains time_line "system" then
    begin
      let time = 
	try 
	  let l_time = String.index time_line 's' in
	  let time_string = String.sub time_line 0 l_time in
	  Time (float_of_string time_string) 
	with Not_found | Failure _ ->
	  errors := IncorrectTime :: (!errors);
	  NoTime
      in
      let max_rss =
	match StringPlus.pos time_line "max rss " with
	| None -> None
	| Some pos_rss ->
	    try 
	      let end_rss = String.index_from time_line (pos_rss+8) 'K' in
	      let rss_string = String.sub time_line (pos_rss+8) (end_rss-pos_rss-8) in
	      Some (int_of_string rss_string)
	    with Not_found | Failure _ ->
	      errors := IncorrectRSS :: (!errors);
	      None
      in
      (!errors, Some (List.rev reversed_result), time, max_rss, time_line ^"\n")
    end
  else
    (TimeNotFound :: (!errors), Some (List.rev (time_line::reversed_result)), NoTime, None, "")
      

(* [get_info_from_script config script] gets the "expected result"
   information from the CryptoVerif or ProVerif file [script].
   [config: config_t] is the configuration associated to CryptoVerif or 
   ProVerif.
   It returns [(errors, result_opt, time, max_rss)] where
   - [errors: error_t list] is a list of errors. 
   - [result_opt: string list option] is the result lines. (It is
   [None] when no result could be found.)
   - [time: time_res_t] is the total runtime of CryptoVerif or ProVerif,
   in seconds. (It is [NoTime] when it is could not be determined and
   [Error] when the script resulted in an error.)
   - [max_rss: int option] is the maximum memory usage, in kb.
   (It is [None] when it could not be determined.) *)
      
let get_info_from_script config script =
  let f = open_in script in
  let errors = ref [] in
  let rec collect_result accu =
    try
      let l = input_line f in
      if StringPlus.contains l "END" then
	accu
      else
	collect_result (l::accu)
    with End_of_file ->
      errors := UnfinishedInfo :: (!errors);
      accu
  in
  let rec look_for_expected() =
    let l = input_line f in
    if StringPlus.contains l config.expected_result_marker then
      Some (collect_result [])
    else
      look_for_expected()
  in
  let result =
    try
      look_for_expected()
    with End_of_file ->
      errors := InfoNotFound :: (!errors);
      None				  
  in
  close_in f;
  match result with
  | None -> (!errors, None, NoTime, None)
  | Some [] -> (EmptyInfo :: (!errors), None, NoTime, None)
  | Some (a::l) ->
      let (errors, result, time_opt, rss, _) =
	interpret_time_line errors l a
      in
      (errors, result, time_opt, rss )

(* [update_expected_result config expected_line_opt filename actual_result time_string]
   updates the expected result included in the script file [filename: string].
   [actual_result: string list] is the new result, [time_string: string] is the new time string.
   [expected_line_opt = None] initially.
   [expected_line_opt = Some line] when the analyzed script contains a reference
   EXPECTED ... FILENAME: filename TAG: ...
   Then [line] is that line, and we update the result in the referenced file [filename].
   That's useful when scripts are generated (for instance by m4).
   [config: config_t] is the configuration associated to CryptoVerif or 
   ProVerif. *)

type state_t =
  | WaitEXPECTED
  | WaitEND
  | Found

let output_line f s =
  output_string f s;
  output_string f "\n"
  
let rec update_expected_result config expected_line_opt filename actual_result time_string =
  let f = open_in filename in
  let tmp_name = filename^".tmp" in
  let f_new = open_out tmp_name in
  let state = ref WaitEXPECTED in
  try
    let rec aux() =
      let line = input_line f in
      let expected_found =
	match expected_line_opt with
	| None -> StringPlus.contains line config.expected_result_marker
	| Some expected_line -> line = expected_line
      in
      match !state with
      | WaitEXPECTED ->
	  if expected_found then
	    begin
	      let ref_initial_file =
		if expected_line_opt = None then
		  (* If we are not already in the initial file referred to by 
                     EXPECTED ... FILENAME: filename TAG: ...
		     check whether the current line is such a reference *)
		  let len_filename = String.length " FILENAME: " in
		  let pos_filename = StringPlus.pos line " FILENAME: " in
		  let pos_tag = StringPlus.pos line " TAG: " in
		  match pos_filename, pos_tag with
		  | Some n_filename, Some n_tag ->
		      let pos_end_filename = n_filename + len_filename in
		      if pos_end_filename < n_tag then
		        (* Line EXPECTED ...  FILENAME: filename TAG: ... *)
			let initial_filename = String.sub line pos_end_filename (n_tag - pos_end_filename) in
			close_out f_new;
			Unix.unlink tmp_name;
			close_in f;
			update_expected_result config (Some line) initial_filename actual_result time_string;
			true
		      else
			false
		  | _ -> false
		else
		  false
	      in
	      if not ref_initial_file then
		begin
		  output_line f_new line;
		  List.iter (output_line f_new) actual_result;
		  output_string f_new time_string;
		  state := WaitEND;
		  aux()
		end
	    end
	  else
	    begin
	      output_line f_new line;
	      aux()
	    end
      | _ when expected_found ->
	  close_in f;
	  close_out f_new;
	  begin
	    match expected_line_opt with
	    | None ->
		error ("Error: script "^filename^" contains several expected results.\n")
	    | Some expected_line ->
		error ("Error: script "^filename^" contains several times an expected result with line.\n"^expected_line^"\n")
	  end
      | WaitEND ->
	  if StringPlus.contains line "END" then
	    begin
	      output_line f_new line;
	      state := Found
	    end;
	  aux()
      | Found ->
	  output_line f_new line;
	  aux()
    in
    aux()
  with End_of_file ->
    close_in f;
    begin
      match !state, expected_line_opt with
      | WaitEXPECTED, Some expected_line ->
	  close_out f_new;
	  error ("Error: expected result with line\n"^expected_line^"\nmissing in "^filename^ "\n")
      | WaitEXPECTED, None ->	  
	  (* expected result not found, add it *)
	  output_line f_new "";
	  output_line f_new ("(* "^config.expected_result_marker);
          List.iter (output_line f_new) actual_result;
          output_string f_new time_string;
          output_line f_new "END *)"
      | Found, _ -> ()
      | WaitEND, _ ->
	  close_out f_new;
	  error ("Error: END marker missing in "^filename^ "\n")
    end;
    close_out f_new;
    Unix.rename tmp_name filename
	
(* [write descr s] writes the string [s] to the file descriptor [descr] *)
	
let write descr s =
  let len = String.length s in
  if Unix.write_substring descr s 0 len <> len then
    error "Error: cannot write file\n"
      
(* [extract_result config output_in_channel] extracts the result
   lines from the output of CryptoVerif or ProVerif. 
   This output is read via the input channel [output_in_channel].
   [config: config_t] is the configuration associated to CryptoVerif or 
   ProVerif. 
   The result lines are returned in reversed order. *)
      
let extract_result config output_in_channel =
  let accu = ref [] in
  let rec aux () =
    let l = input_line output_in_channel in
    if (config.is_result_line l) || (StringPlus.contains l "Error") then
      accu := l::(!accu);
    aux ()
  in
  try 
    aux ()
  with End_of_file ->
    !accu

(* [equal_lists l1 l2] is true when the lists [l1] and [l2] are equal *)
      
let equal_lists l1 l2 =
  (List.length l1 == List.length l2) &&
  (List.for_all2 (=) l1 l2)

(* [files_t] contains the file descriptors and channels used for analyzing
   scripts *)

type files_t =
    { null_input_file_descr : Unix.file_descr;
         (* null input file descriptor, used as input for CryptoVerif or ProVerif *)
      output_file_descr : Unix.file_descr;
         (* output file descriptor, used to store the output of CryptoVerif or ProVerif *)
      output_in_channel : in_channel;
         (* input channel used to read the output of CryptoVerif or ProVerif.
	    Points to the same file as [output_file_descr] *)
      res_out_channel : out_channel;
         (* output channel used to output the results of tests (for each test,
	    whether it yields the expected result or not). The same output
	    it also displayed on the standard output. *)
      sum_out_channel : out_channel
         (* output channel used to output a summary of the result 
	    (for each test, the result lines and runtime of CryptoVerif 
	    or ProVerif). *) }

(* [analyze_file config options filename files] analyzes the script
   stored in file [filename].
   [config: config_t] is the configuration associated to CryptoVerif or 
   ProVerif. 
   [options: string list] is a list of options passed to CryptoVerif or 
   ProVerif.
   [files: files_t] describes auxiliary files (see type [files_t])
   *)
      
let analyze_file config mode options filename files =
  let sum_out s =
    output_string files.sum_out_channel s
  in
  let res_out s =
    print_string s; flush stdout_channel;
    output_string files.res_out_channel s
  in
  let (file_info_errors, expected_result_opt, expected_time_opt, expected_rss_opt) =
    get_info_from_script config filename
  in
  if (mode == Add) && (expected_result_opt <> None) then () else
  begin
    res_out ("PROTOCOL " ^ filename ^ " ");
    write files.output_file_descr ("PROTOCOL " ^ filename ^ "\n");
    let output_length = in_channel_length files.output_in_channel in
    let args = Array.make (List.length options + 2) filename in
    args.(0) <- config.executable;
    List.iteri (fun n s -> args.(n+1) <- s) options;

    let (actual_errors, actual_result_opt, actual_time_opt, actual_rss_opt, time_string, time_line) =
      if Sys.os_type <> "Unix" then
	let normal_result start_time end_time status =
	  seek_in files.output_in_channel output_length;
	  let reversed_result = extract_result config files.output_in_channel in
	  match status with
	  | WEXITED 0 ->
	      let time = end_time -. start_time in
	      let time_line = Printf.sprintf "%.3fs (elapsed: user + system + other processes)" time in
	      ([], Some (List.rev reversed_result), Time(time), None, time_line^"\n", time_line)
	  | _ -> 
	      let error_line =
		match status with
		| WEXITED status -> Printf.sprintf "xtime: error in child process (status : %i)" status
		| WSIGNALED _ -> "xtime: killed by a signal"
		| WSTOPPED _ -> "xtime: stopped"
	      in
	      ([], Some (List.rev (error_line::reversed_result)), Error, None, "", error_line)
	in	  
	let start_time = Unix.gettimeofday() in
	let child_pid = Unix.create_process config.executable args
	    files.null_input_file_descr files.output_file_descr files.output_file_descr in
	if (!timeout) > 0 then
	  begin
	    let timeout_reached = ref false in
	    let (pipe_read, pipe_write) = Unix.pipe() in
	    let _ = Thread.create (fun () ->
	      let (read_ready, _, _) = Unix.select [pipe_read] [] [] (float_of_int (!timeout)) in
	      match read_ready with
	      | [] ->
		  timeout_reached := true;
		  begin
		    try
		      Unix.kill child_pid Sys.sigkill
		    with _ -> ()
		  end;
		  Unix.close pipe_read
	      | _ ->
		  Unix.close pipe_read
		    ) ()
	    in
	    let (_, status) = Unix.waitpid [] child_pid in
	    let end_time = Unix.gettimeofday() in
	    if (!timeout_reached) then
	      begin
		Unix.close pipe_write;
		let time_line = "xtime: timeout ("^(string_of_int (!timeout))^" s)" in
		([TimeOut], None, NoTime, None, time_line ^"\n", time_line)
	      end
	    else
	      begin
		begin
		  try
		    ignore (Unix.single_write_substring pipe_write "f" 0 1)
		  with _ -> ()
		end;
		Unix.close pipe_write;		
		normal_result start_time end_time status
	      end
	  end
	else
	  begin
	    let (_, status) = Unix.waitpid [] child_pid in
	    let end_time = Unix.gettimeofday() in
	    normal_result start_time end_time status
	  end
      else
	let time_record = { total = -1.; user = -1.; system = -1. } in
	let time_filename = Filename.concat (!tmpdir) "time" in
	let time_out_channel = open_out time_filename in
	flush files.res_out_channel; (* flush before the fork to avoid double outputs; 
          sum_out_channel is flushed immediately after the outputs are made, no need to flush again. *)
	let fork_res = Unix.fork() in
	if fork_res = 0 then
	  begin
	  (* Child process *)
	  try
	    let child_pid = Unix.create_process config.executable args
		files.null_input_file_descr files.output_file_descr files.output_file_descr
	    in
	    let normal_result status =
	      begin
		match status with
		| WEXITED 0 ->
		    let max_rss = get_resources(time_record) in
		    Printf.fprintf time_out_channel "%.3fs (user %.3fs + system %.3fs), max rss %iK\n" time_record.total time_record.user time_record.system max_rss
		| WEXITED 127 ->
		(* Could not execute the program *)
		    exit 3
		| WEXITED status ->
		    Printf.fprintf time_out_channel "xtime: error in child process (status : %i)\n" status
		| WSIGNALED _ ->
		    output_string time_out_channel "xtime: killed by a signal\n"
		| WSTOPPED _ ->
		    output_string time_out_channel "xtime: stopped\n"
	      end;
	      flush time_out_channel;
	      exit 0
	    in
	    if (!timeout) > 0 then
	      begin
		let fork_res_sleep = Unix.fork() in
		if fork_res_sleep = 0 then
                  begin
		    (* Child process *)
		    Unix.sleep (!timeout);
		    exit 0
		  end
		else
		  begin
		    (* Parent process *)
      		    let (pid_finished, status) = Unix.waitpid [] (-1) in
		    if pid_finished == fork_res_sleep then
		      begin
		        (* Timeout *)
			begin
			  try
			    Unix.kill child_pid Sys.sigkill
			  with _ -> ()
			end;
			let _ = Unix.waitpid [] child_pid in
			output_string time_out_channel ("xtime: timeout ("^(string_of_int (!timeout))^" s)\n");
			flush time_out_channel;
			exit 0
		      end
		    else
		      begin
			assert (pid_finished == child_pid);
			begin
			  try 
			    Unix.kill fork_res_sleep Sys.sigkill
			  with _ -> ()
			end;
			let _ = Unix.waitpid [] fork_res_sleep in
			normal_result status
		      end
		  end
	      end
	    else
	      begin
		let (_, status) = Unix.waitpid [] child_pid in
		normal_result status
	      end
	  with _ -> exit 2
	  end
	else
	  begin
	    (* Parent process *)
	    close_out time_out_channel;
      	    let (_, status) = Unix.waitpid [] fork_res in
	    begin
	      match status with
	      | WEXITED 0 -> () (* child process ran fine *)
	      | WEXITED 3 -> error ("Error: cannot execute "^config.executable^"\n")
	      | _ ->  error "Error: problem in child process\n"
	    end;
	    let time_in_channel = open_in time_filename in
	    let time_line = input_line time_in_channel in
	    close_in time_in_channel;
	    seek_in files.output_in_channel output_length;
	    let reversed_result = extract_result config files.output_in_channel in
	    let (actual_errors, actual_result_opt, actual_time_opt, actual_rss_opt, time_string) =	
	      interpret_time_line (ref []) reversed_result time_line
	    in
	    (actual_errors, actual_result_opt, actual_time_opt, actual_rss_opt, time_string, time_line)
	  end
    in
    let equal_result =
      match expected_result_opt, actual_result_opt with
      | None, _ | _, None -> false
      | Some expected_result, Some actual_result ->
	  equal_lists actual_result expected_result
    in
    begin
      if equal_result then
	res_out "OK\n"
      else if List.mem TimeOut actual_errors then
	res_out "TIMEOUT\n"
      else
	res_out "\n"
    end;
    List.iter (function
      | InfoNotFound -> if mode == Test then res_out "ERROR: expected result missing in script file\n"
      | EmptyInfo -> if mode == Test then res_out "ERROR: empty expected result in script file\n"
      | UnfinishedInfo -> res_out "ERROR: END marker missing in script file\n"
      | TimeNotFound -> res_out "Expected runtime not found in script file\n"
      | IncorrectTime -> res_out "ERROR: Incorrectly formatted runtime in script file\n" 
      | IncorrectRSS -> res_out "ERROR: Incorrectly formatted max rss in script file\n"
      | TimeOut -> assert false
	    ) file_info_errors;
    List.iter (function
      | TimeNotFound -> res_out "ERROR: Expected runtime not found in output of xtime\n"
      | IncorrectTime -> res_out "ERROR: Incorrectly formatted runtime in output of xtime\n" 
      | IncorrectRSS -> res_out "ERROR: Incorrectly formatted max rss in output of xtime\n"
      | TimeOut -> ()
      | _ -> assert false
	    ) actual_errors;
    begin
      match actual_result_opt with
      | Some actual_result ->
	  begin
	    match expected_result_opt with
	    | None ->
		if mode <> Test then
		  res_out "Adding result to script. ";
		res_out "Actual result:\n";
		List.iter (fun s -> res_out s; res_out "\n") actual_result
	    | Some expected_result ->
		if not equal_result then
		  begin
		    if mode == Update then
		      res_out "Updating expected result. Old:\n"
		    else
		      res_out "RESULTS DIFFER! Expected:\n";
		    List.iter (fun s -> res_out s; res_out "\n") expected_result;
		    res_out "Actual:\n";
		    List.iter (fun s -> res_out s; res_out "\n") actual_result
		  end
	  end;
	  if (mode == Update) || (mode <> Test && expected_result_opt == None) then
	    update_expected_result config None filename actual_result time_string
      | None -> ()
    end;
    begin
      match actual_time_opt, expected_time_opt with
      | Time time, Time expected_time ->
	  if expected_time *. 1.2 +. 0.2 < time then
	    res_out (Printf.sprintf "Slower: old=%.3fs new=%.3fs\n" expected_time time)
	  else if expected_time *. 0.8 -. 0.2 > time then
	    res_out (Printf.sprintf "Faster: old=%.3fs new=%.3fs\n" expected_time time)
      | Time time, NoTime ->
	  res_out (Printf.sprintf "Actual time: %.3fs\n" time)
      | _ -> ()
    end;
    begin
      match actual_rss_opt, expected_rss_opt with
      | Some actual_rss, Some expected_rss ->
	  if (float_of_int expected_rss) *. 1.2 +. 10000. < float_of_int actual_rss then
	    res_out (Printf.sprintf "More memory: old=%iK new=%iK\n" expected_rss actual_rss)
	  else if (float_of_int expected_rss) *. 0.8 -. 10000. > float_of_int actual_rss then
	    res_out (Printf.sprintf "Less memory: old=%iK new=%iK\n" expected_rss actual_rss)
      | _ -> ()
    end;
    write files.output_file_descr time_line;
    write files.output_file_descr "\n";
    sum_out "PROTOCOL ";
    sum_out filename;
    sum_out "\n";
    begin
      match actual_result_opt with
      | Some actual_result -> List.iter (fun s -> sum_out s; sum_out "\n") actual_result
      | None -> ()
    end;
    sum_out time_string;
    flush files.sum_out_channel;
    flush files.res_out_channel
  end
    
(* [get_date()] returns the current date as a string (for use in filenames) *)
    
let get_date() =
  let tm = Unix.localtime(Unix.time()) in
  Printf.sprintf "%04i.%02i.%02i-%02i_%02i_%02i" (tm.tm_year+1900)
    (tm.tm_mon+1) tm.tm_mday tm.tm_hour tm.tm_min tm.tm_sec

(* [open_files prefix] opens auxiliary files.
   [prefix: string] is a string used a prefix in the filenames.
   It returns a record [files_t]. *)
    
let open_files prefix =
  let output = prefix ^ (get_date()) in
  let output_file_descr = Unix.openfile (Filename.concat "tests" output) [O_WRONLY;O_APPEND;O_CREAT] 0o640 in
  let output_in_channel = open_in (Filename.concat "tests" output) in
  { null_input_file_descr = Unix.openfile (Filename.concat (!tmpdir) "null") [O_RDONLY;O_CREAT;O_TRUNC] 0o600;
    output_file_descr = output_file_descr;
    output_in_channel = output_in_channel;
    res_out_channel = open_out_gen [Open_append; Open_creat] 0o640 (Filename.concat "tests" ("res-"^output));
    sum_out_channel = open_out_gen [Open_append; Open_creat] 0o640 (Filename.concat "tests" ("sum-"^output)) }

(* [close_files files] closes the files in [files: files_t] *)
    
let close_files files =
  Unix.close files.null_input_file_descr;
  Unix.close files.output_file_descr;
  close_in files.output_in_channel;
  close_out files.res_out_channel;
  close_out files.sum_out_channel

(* [analyze_dir config dirname files filename_opt] analyzes files
   in the directory [dirname]. 
   When [filename_opt = None], it analyzes all suitable files in 
   [dirname] and subdirectories.
   When [filename_opt = Some filename], it analyzes only the file [filename].
   [config: config_t] is the configuration associated to CryptoVerif or 
   ProVerif. 
   [files: files_t] describes auxiliary files (see type [files_t]) *)
    
let analyze_dir config mode dirname files filename_opt =
  let res_out s =
    print_string s; flush stdout_channel;
    output_string files.res_out_channel s
  in
  res_out "\nDirectory ";
  res_out dirname;
  res_out "\n\n";
  let all_options = config.build_option_table dirname in
  let analyze_one_file full_filename filename =
    let rec find_options = function
	[] -> ()
      | (ext, options)::rest -> 
	  if StringPlus.case_insensitive_ends_with filename ext then
	    analyze_file config mode ((!additional_options) @ options) full_filename files
	  else
	    find_options rest
    in
    find_options all_options
  in
  let rec aux dirname =
    let file_array = Sys.readdir dirname in
    Array.sort compare file_array;
    Array.iter (fun filename ->
      let full_filename = Filename.concat dirname filename in
      try 
	if Sys.is_directory full_filename then
	  aux full_filename
	else if StringPlus.case_insensitive_contains filename ".m4." ||
                StringPlus.case_insensitive_contains filename ".out." then
	  ()
	else
	  try 
	    analyze_one_file full_filename filename
	  with Sys_error s ->
	    error ("Error: "^s^"\n")
      with Sys_error _ ->
	res_out ("Warning: File "^full_filename^" was probably removed.\n")
	    ) file_array
  in
  match filename_opt with
  | None -> aux dirname
  | Some filename ->
      let full_filename = Filename.concat dirname filename in
      analyze_one_file full_filename filename

(* [usage()] displays an help message. Called when the arguments are 
   incorrect *)
	
let usage() =
  print_string
    "Incorrect arguments
Usage: 
  analyze [options] <prog> <mode> <tmp_directory> <prefix for output files> dirs <directories>
  analyze [options] <prog> <mode> <tmp_directory> <prefix for output files> file <directory> <filename>
where 
* [options] can be 
  - -timeout <n>: sets the time out to <n> seconds.
  - -progopt <arguments to pass to the tested program> -endprogopt
* <prog> is either CV for CryptoVerif or PV for ProVerif
* and <mode> can be
  - test: test the mentioned scripts
  - test_add: test the mentioned scripts and add the 
    expected result in the script when it is missing
  - add: add the expected result in the script when it is missing, 
    do not test scripts that already have an expected result
  - update: test the mentioned scripts and update the expected
    result in the script.";
  exit 0

(* Main function. Parses command-line arguments. *)
    
let _ =
  let rec parse_options n =
    if Array.length Sys.argv < (n+1) then
      usage();
    match Sys.argv.(n) with
    | "-timeout" ->
	if Array.length Sys.argv < (n+2) then
	  usage();
	begin
	  try
	    timeout := int_of_string (Sys.argv.(n+1))
	  with Failure _ ->
	    usage()
	end;
	parse_options (n+2)
    | "-progopt" ->
	let rec aux accu n =
	  if Array.length Sys.argv < (n+1) then
	    usage();
	  match Sys.argv.(n) with
	  | "-endprogopt" ->
	      additional_options := List.rev accu;
	      parse_options (n+1)
	  | s -> aux (s::accu) (n+1)
	in
	aux [] (n+1)
    | _ -> n
  in
  let n = parse_options 1 in
  try 
    if Array.length Sys.argv < (n+6) then
      usage();
    let config =
      match Sys.argv.(n) with
      | "CV" -> cv_config()
      | "PV" -> pv_config()
      | _ -> usage()
    in
    let mode =
      match Sys.argv.(n+1) with
      | "test" -> Test
      | "test_add" -> TestAdd
      | "add" -> Add
      | "update" -> Update
      | _ -> usage()
    in
    tmpdir := Sys.argv.(n+2);
    let prefix = Sys.argv.(n+3) in
    match Sys.argv.(n+4) with
    | "dirs" ->
	let files = open_files prefix in
	for i = n+5 to Array.length Sys.argv-1 do
	  let s = Sys.argv.(i) in
	  if (try Sys.is_directory s with Sys_error _ -> false) then
	    analyze_dir config mode s files None
	done;
	close_files files
    | "file" ->
	if Array.length Sys.argv <> n+7 then
	  usage();
	let files = open_files prefix in
	analyze_dir config mode Sys.argv.(n+5) files (Some (Sys.argv.(n+6)));
	close_files files
    | _ ->
	usage()
  with
   | Unix.Unix_error(e, fct, arg) ->
      error ("Error: "^(Unix.error_message e)^", found in fct "^fct^
        (if arg = "" then "\n" else "("^arg^", ...)\n"))
   | Sys_error s ->
      error ("Error: "^s^"\n")
   | e -> 
      error ("Error: "^(Printexc.to_string e)^"\n")
