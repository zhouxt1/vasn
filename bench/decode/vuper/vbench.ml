(* VUPER's DL-DCCH-MessageType decoder on a directory of UPER messages
   (build.sh ul: its UL-DCCH-MessageType one, as vbench_ul).

     vbench DIR ROUNDS

   The decoder is VUPER's extracted OCaml, unchanged (FormatTest.ml, from
   VUPER/diff_test/fuzz/ocaml_test). Every message is read into a Bigarray
   first; a round parses each message once and drops the value, and the
   round, not each message, is timed with a monotonic clock. Prints how many
   decoded, and the fastest and median round -- the same as bench_asn1c. *)
open Formats

let pos0 = { FormatTest.byte_pos = 0; FormatTest.byte_off = I0 }

let load dir =
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".uper")
  |> List.sort compare
  |> List.map (fun f ->
         let ic = open_in_bin (Filename.concat dir f) in
         let n = in_channel_length ic in
         let s = really_input_string ic n in
         close_in ic;
         let ba = BigArrayExtr.make n '\x00' in
         String.iteri (fun i c -> Bigarray.Array1.set ba.buffer i c) s;
         ba)
  |> Array.of_list

let () =
  let dir = Sys.argv.(1) and rounds = int_of_string Sys.argv.(2) in
  let msgs = load dir in
  let n = Array.length msgs in
  let times = Array.make rounds 0. in
  let ok = ref 0 in
  for r = -1 to rounds - 1 do  (* round -1 warms up *)
    let good = ref 0 in
    let t0 = Mtime_clock.now () in
    Array.iter
      (fun ba ->
        match FormatTest.dL_DCCH_MessageType__Format.t_Parse ba pos0 with
        | Some _ -> incr good
        | None -> ())
      msgs;
    let dt = Mtime.Span.to_float_ns (Mtime.span t0 (Mtime_clock.now ())) in
    if r >= 0 then times.(r) <- dt;
    ok := !good
  done;
  Array.sort compare times;
  Printf.printf "vuper %d messages, %d decoded, min %.1f ns/msg, median %.1f ns/msg\n" n !ok
    (times.(0) /. float n) (times.(rounds / 2) /. float n)
