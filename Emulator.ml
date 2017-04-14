(* Micha�l P�RIN, Verimag / Universit� Grenoble-Alpes, F�vrier 2017
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * (PROJECT 2019)  1. Multi-Bands Turing Machines working on a an alphabet A can be simulated by a single band Turing Machine using a augmented Alphbet A'
 *
 * (PROJECT 2017)  2. A Turing Machine using an alphabet A can be simulated by a Turing Machine using the binary alphabet {B,D}
 *
 * This module provides means to write Emulator for Problems 1 and 2.
 *
*)



open Tricks
open State
open Action
open Transition
open Band
open Configuration
open Turing_Machine
open Execution




type emulator   = State.t * Action.t * State.t -> Turing_Machine.t
type translator = Band.t list -> Band.t list

type simulator  =
  { name: string ;
    encoder: translator ;
    decoder: translator ;
    emulator: emulator
  }

type simulators = simulator list


module Simulator =
  (struct

    type loggers = Logger.t list

    let (fake_tm_named: string ->  Turing_Machine.t) = fun name ->
      Turing_Machine.finalize name Turing_Machine.nop

    let (show_bands_using: loggers -> string -> Band.t list -> Band.t list) = fun loggers name bands ->
      begin
        (Configuration.make (fake_tm_named name) bands) >> (Configuration.print_using loggers) ;
        bands
      end

    let rec (execute_action_using: simulators * loggers -> (State.t * Action.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (src,action,tgt) cfg ->
      let cfg = cfg >> (Configuration.show_using loggers)
      in
      let next_bands =
        match simulators with
        | [] -> Action.perform action cfg.bands

        | simulator :: other_simulators
          ->
          let e_tm    = simulator.emulator (src,action,tgt)
          and e_bands = (simulator.encoder  cfg.bands) >> (show_bands_using loggers (String.concat " to " [ "encoding" ; simulator.name ]))
          in let e_cfg = Configuration.make e_tm e_bands
          in
          let e_next_cfg = log_run_using (other_simulators,loggers) e_cfg
          in
          let bands_updated_by_emulation = (simulator.decoder e_next_cfg.bands) >> (show_bands_using loggers (String.concat " " [ simulator.name ; "decoding"]))
          in
          let bands_updated_by_execution = Action.perform action cfg.bands
          in
          if (* FIXME: Band.are_equivalents *) bands_updated_by_execution = bands_updated_by_emulation
          then bands_updated_by_execution
          else failwith
              (String.concat "\n" [ "execute_action_using: simulation errors" ;
                                    Band.to_ascii_many bands_updated_by_emulation ;
                                    "are not equivalent to" ;
                                    Band.to_ascii_many bands_updated_by_execution ;
                                  ])
      in
      { cfg with bands = next_bands }


    and (execute_single_band_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Band.t -> Band.t) = fun (simulators,loggers) (src,instruction,tgt) band ->
      let cfg = Configuration.make (fake_tm_named (Instruction.pretty instruction)) [band]
      in let next_cfg = execute_instruction_using (simulators,loggers) (src,instruction,tgt) cfg
      in List.hd next_cfg.bands

    and (execute_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
      (match instruction with
       | Run tm -> (* FIXME: ajoutez les transitions (source -nop-> init) et (accept -nop-> target) *)
         run_using (simulators,loggers) (Configuration.make tm cfg.bands)

       | Seq [] -> cfg
       | Seq (inst::instructions) ->
         let intermediate_state = State.fresh_from source in
         cfg
         >> (execute_instruction_using (simulators,loggers) (source, inst, intermediate_state))
         >> (execute_instruction_using (simulators,loggers) (intermediate_state, Seq instructions, target))

       | Parallel instructions ->
         let next_bands =
           List.map
             (fun (inst,band) -> execute_single_band_instruction_using (simulators,loggers) (source,inst,target) band)
             (Instruction.zip instructions cfg.bands)
         in { cfg with bands = next_bands }

       | Action action -> execute_action_using (simulators,loggers) (source,action,target) cfg
      )

    and (execute_transition_using: simulators * loggers -> Transition.t -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
      let next_cfg = execute_instruction_using (simulators,loggers) (source,instruction,target) cfg
      in { next_cfg with state = target}

    and (run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
      match Execution.select_enabled_transition cfg.tm cfg with
      | None -> cfg
      | Some transition ->
        let next_cfg = execute_transition_using (simulators,loggers) transition cfg
        in run_using (simulators,loggers) next_cfg

    and (log_run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
      let loggers = cfg.logger :: loggers
      in
      let final_cfg = (run_using (simulators,loggers) cfg) >> (Configuration.show_using loggers)
      in
      begin
        cfg.logger#close ;
        final_cfg
      end

  end)


open State
open Symbol
open Alphabet
open Pattern
open Action
open Band
open Transition
open Turing_Machine
open MyList

(* An example of a useless but correct translation that splits the effect of a transition into three steps

   (q) -- l / e : d --> (q')
   ===
   (q) -- l : H --> (q.0) -- ANY / e : H --> (q.00) -- ANY : d --> (q')
*)


module Split =
  (struct

    (* TRANSLATION OF BANDS *)

    let (encode: translator) = fun x -> x

    (* REVERSE TRANSLATION *)

    let (decode: translator) = fun x -> x

    (* EMULATION OF TRANSITIONS *)

    let (just_read: reading -> Action.t) = fun reading ->
      RWM (reading, No_Write, Here)

    let (just_write: writing -> Action.t) = fun writing ->
      match writing with
      | No_Write     -> Nop
      | Write symbol -> RWM (Match(ANY), Write symbol, Here)

    let (just_move: moving -> Action.t) = fun moving ->
      RWM (Match(ANY), No_Write, moving)

    let (synchronize: Action.t list -> Instruction.t) = fun actionS ->
      let rec (rec_synchronize: ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun (reads,writes,moves) actions ->
        match actions with
        | [] -> (List.rev reads, List.rev writes, List.rev moves)
        | action::actions ->
          (match action with
           | Nop        -> rec_synchronize ( Nop::reads , Nop::writes , Nop::moves) actions
           | RWM(r,w,m) -> rec_synchronize ( (just_read r)::reads , (just_write w)::writes , (just_move m)::moves) actions
           | Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
          )
      in
      let (reads,writes,moves) = rec_synchronize ([],[],[]) actionS
      in
      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]

    let rec (transitions_emulating: State.t * Action.t * State.t -> Transition.t list) = fun (source,action,target) ->
      (match action with
       | Nop -> [ (source, Action(Nop), target) ]

       | RWM(r,w,m) -> [ (source, Seq[ Action(just_read r) ; Action(just_write w) ; Action(just_move m) ], target) ]

       | Simultaneous actions -> [ (source, synchronize actions, target) ]
      )

    and (emulate_action: emulator) = fun (source,action,target) ->
      let (source,target) =
        if source <> target   (* /!\ loop in the emulated TM if source-target *)
        then (source,target)
        else (State.initial, State.accept)
      in
      let transitions =  transitions_emulating (source,action,target) in
      { Turing_Machine.nop with
        name = String.concat "" [ "Split" ; Pretty.parentheses (Transition.to_ascii (source,Action action, target)) ] ;
        initial = source ;
        accept  = target ;
        transitions = transitions
      }

    (* THE SIMULATOR *)

    let (* USER *) (simulator: simulator) = { name = "Split" ; encoder = encode ;  decoder = decode ; emulator = emulate_action }

  end)



module Binary =
struct

  (* TRANSLATION OF BANDS *)

  (* The modules Bit and Bits are defined in Alphabet.ml *)

  (** NEW 27/03/2107 *)
  type encoding = (Symbol.t * Bits.t) list

  (** NEW 27/03/2107 *)



  (*let build_encoding_v1 : Alphabet.t -> encoding
  (* PROJET 2017: modifiez ce code -> *)
    = fun alphabet ->
      let symbol_to_bits : Symbol.t -> Bits.t
        = fun symbol ->
        match symbol with
        |B -> [Bit.zero ; Bit.zero ; Bit.zero ; Bit.zero]
        |D -> [Bit.zero ; Bit.zero ; Bit.zero ; Bit.unit]
        |Z -> [Bit.zero ; Bit.zero ; Bit.unit ; Bit.zero]
        |U -> [Bit.zero ; Bit.zero ; Bit.unit ; Bit.unit]
        |S -> [Bit.zero ; Bit.unit ; Bit.zero ; Bit.zero]
        |L -> [Bit.zero ; Bit.unit ; Bit.zero ; Bit.unit]
        |O -> [Bit.zero ; Bit.unit ; Bit.unit ; Bit.zero]
        |C -> [Bit.zero ; Bit.unit ; Bit.unit ; Bit.unit]
        |X -> [Bit.unit ; Bit.zero ; Bit.zero ; Bit.zero]
      in
      List.map (fun symbol -> (symbol, symbol_to_bits symbol)) alphabet.symbols*)

  (*let build_encoding_v2  :Alphabet.t -> encoding
  (* PROJET 2017: modifiez ce code -> *)
    = fun alphabet ->
    let enumere = Bit_Vector.Made_Of(Bit).enumerate alphabet.symbol_size_in_bits
    in
    let rec atribution : Symbol.t list -> encoding
      = fun symbols ->
      match symbols with
      | [] -> (List.hd , (List.hd enumere))
      | _ -> (List.hd , (List.tl enumere)) :: (atribution (List.tl symbols)
    in
    atribution alphabet.symbols*)

  let build_encoding  :Alphabet.t -> encoding
  (* PROJET 2017: modifiez ce code -> *)
    = fun alphabet ->
    let taille = (List.length (Alphabet.symbols_of alphabet)) in
    List.combine alphabet.symbols (Bits.enumerate taille)

  let get_symbole_from_bits : Symbol.t list -> encoding -> Symbol.t
  = fun bits encodage -> try (fst (List.find (fun encod -> snd encod = bits) encodage)) with Not_found -> B

  let get_bits_from_symbole : Symbol.t -> encoding -> Bits.t
  = fun symb encodage -> (snd (List.find (fun encod -> fst encod = symb) encodage))

  (** MODIFIED 27/03/2107 *)
  (*let encode_with_v1 : encoding -> Band.t list -> Band.t list
  (* PROJET 2017: modifiez ce code -> *)
    = fun encoding bands ->
      let rec encode_bande :Band.t -> Band.t =
        fun band ->
        match band.right with
        | [] -> band
        | _ -> encode_bande (Band.move_head_right (Band.ecrire_symbole_en_bits band (get_bits_from_symbole band.head encoding) ))

      in
      List.map (fun band -> encode_bande (rembobine_gauche band)) bands*)

  let encode_with : encoding -> Band.t list -> Band.t list
  (* PROJET 2017: modifiez ce code -> *)
    = fun encoding bands ->

      let rec encode_list : Symbol.t list -> Bits.t
        = fun symbs ->
        match symbs with
        | [] -> []
        | s::ymbs -> (encode_list ymbs) @ (get_bits_from_symbole s encoding)
      in

      let encode_bande :Band.t -> Band.t =
        fun bande -> {
          bande with left = encode_list bande.left ;
          head = List.hd (get_bits_from_symbole bande.head encoding);
          right = (List.tl (get_bits_from_symbole bande.head encoding)) @ (encode_list bande.right)
        }

      in
      List.map (fun bande -> encode_bande bande) bands


  (* REVERSE TRANSLATION *)

  (** MODIFIED 27/03/2107 *)
  (*let decode_with_v1 : encoding -> Band.t list -> Band.t list
(* PROJET 2017: modifiez ce code -> *)
  = fun encoding bands->
    let rec prochain_symbol : Bits.t -> Band.t -> (Symbol.t * Band.t) =
      fun bits bande ->
      try ((fst (List.find (fun encodage -> snd encodage = bits) encoding)), bande)
      with
      Not_found -> prochain_symbol (bits@[bande.head]) (Band.move_head_right_avec_suppression_gauche bande)
    in
    let rec decode_bande : Band.t -> Band.t =
      fun bande ->
      match bande.right with
      | [] -> bande
      | _ -> let iterateur = prochain_symbol (bande.head::[]) bande in
              let b = Band.write (fst iterateur) in
                decode_bande (snd iterateur)
    in
    List.map (fun band -> decode_bande (rembobine_gauche band)) bands*)


  let decode_with : encoding -> Band.t list -> Band.t list
  (* PROJET 2017: modifiez ce code -> *)
    = fun encoding bands->

    let rec decode_list : Symbol.t list -> Symbol.t list
      = fun bits ->
      match bits with
      | [] -> []
      | _ -> let bande = (MyList.split_at (List.length (snd (List.hd encoding))) bits) in
            (get_symbole_from_bits (fst bande) encoding) :: (decode_list (snd bande))
    in

    let rec decode_bande : Band.t -> Band.t =
      fun bande -> {
        bande with left = decode_list bande.left;
        head = get_symbole_from_bits (bande.head :: (fst (MyList.split_at (List.length (snd (List.hd encoding)) - 1) bande.right))) encoding;
        right = decode_list (snd (MyList.split_at (List.length (snd (List.hd encoding)) - 1) bande.right))
        }
    in

    List.map (fun bande -> decode_bande bande) bands




  (* EMULATION OF TRANSITIONS *)

  let (emulate_action: State.t * Action.t * State.t -> Turing_Machine.t)
  (* PROJET 2017: modifiez ce code -> *)
    = fun (source,action,target) ->
      { Turing_Machine.nop with
        name = String.concat "" [ "Binary" ; Pretty.parentheses (Action.to_ascii action) ] ;
        initial = State.initial ;
        accept  = State.accept ;
        transitions = [(State.initial,Action(action),State.accept)]
      }

  (* THE SIMULATOR *)

  (** MODIFIED 27/03/2107 *)
  let make_simulator : Alphabet.t -> simulator
    = fun alphabet ->
      let encoding = build_encoding alphabet in
      { name = "Binary" ;
        encoder = encode_with encoding ;
        decoder = decode_with encoding ;
        emulator = emulate_action
      }

end


(* DEMO *)

open Alphabet

let (demo: unit -> unit) = fun () ->
  let alphabet = Alphabet.make [B;Z;U] in
  let band = Band.make alphabet [U;U;Z;U] in

  let encodage = Binary.build_encoding alphabet in
  let band_code = List.hd (Binary.encode_with encodage [band]) in
  let band_decode = List.hd (Binary.decode_with encodage [band]) in

  let tm = Turing_Machine.incr in
  let cfg = Configuration.make tm [ band ] in
  let _final_cfg = Simulator.log_run_using
      ([ (* Split.simulator ; *)
        (** MODIFIED 27/03/2107 *) (*Binary.make_simulator alphabet*)
      ],[])
      cfg
  in (
    print_string "Bande avant encodage : ";
    print_string (Band.to_ascii band);

    print_string "\nBande apres encodage : ";
    print_string (Band.to_ascii band_code);

    print_string "\nBande apres decodage : ";
    print_string (Band.to_ascii band_decode);

    print_string "\n"
    )

  (*
  let (demo: unit -> unit) = fun () ->
    let alphabet = Alphabet.make [B;Z;U] in
    let band = Band.make alphabet [U;U;Z;U] in
    let tm = Turing_Machine.incr in
    let cfg = Configuration.make tm [ band ] in
    let _final_cfg = Simulator.log_run_using
        ([ (* Split.simulator ; *)
          (** MODIFIED 27/03/2107 *) Binary.make_simulator alphabet
        ],[])
        cfg
    in ()
  *)
