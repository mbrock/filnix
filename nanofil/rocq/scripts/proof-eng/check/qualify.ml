(* Keep every global reference's absolute name, including references hidden by
   notations and implicit arguments when the caller enables Printing All. *)
let () =
  Constrextern.set_extern_reference
    (fun ?loc _ reference ->
      let reference = Names.GlobRef.canonize reference in
      Libnames.qualid_of_path ?loc (Nametab.path_of_global reference))
