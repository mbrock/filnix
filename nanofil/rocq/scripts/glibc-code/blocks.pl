/* This command describes block-entry environments in a linked module term.
   It reuses the compiler's CFG and phi-aware liveness analyses rather than
   guessing dependencies from Gallina text or a block's position in a file.

   ```sh
   swipl blocks.pl MODULE.term FUNCTION
   ```

   A proof must distinguish values a block preserves from values it creates.
   The JSON reports both sets so authors do not require new variables to equal
   their old bindings.
*/
:- use_module('../../../src/cfg').
:- use_module(library(http/json)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, [File, Name]),
    read_file_to_terms(File, [module(Items)], [encoding(utf8)]),
    ( memberchk(func(Name, _, _, _, Blocks), Items) -> true
    ; throw(error(existence_error(function, Name), blocks)) ),
    % The analyses must not silently skip an instruction they do not know.
    forall(member(block(_, Phis, Insts, Jump), Blocks),
           ( forall(member(Phi, Phis), (Phi = phi(tmp(_), _, Pairs), is_list(Pairs))),
             forall(member(I, Insts),
                    ( once(inst_uses(I, _)) -> true
                    ; throw(error(domain_error(instruction, I), blocks)) )),
             ( jump_succs(Jump, _) -> true
             ; throw(error(domain_error(jump, Jump), blocks)) ) )),
    func_cfg(Blocks, Cfg), Cfg = cfg(Entry, _, Succs, Preds),
    blocks_gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    liveness(Cfg, GenKill, EdgeUses, _, LiveOut),
    findall(Row,
            ( member(block(L, Phis, _, _), Blocks),
              get_assoc(L, Preds, Ps), get_assoc(L, Succs, Ss),
              get_assoc(L, GenKill, Reads-Writes), get_assoc(L, LiveOut, Out),
              ord_subtract(Out, Writes, Keeps), ord_intersection(Out, Writes, Outputs),
              findall(E,
                      ( member(P, Ps),
                        ( get_assoc(P-L, EdgeUses, Us) -> true ; Us = [] ),
                        ord_union(Reads, Us, Input),
                        atom_string(P, From), strings(Input, Inputs),
                        E = _{predecessor:From, reads:Inputs} ), Edges),
              ( L == Entry ->
                  ( Phis == [] -> true ; throw(error(domain_error(entry_phis, Phis), blocks)) ),
                  strings(Reads, Inputs), Entries = [_{predecessor:null, reads:Inputs}|Edges]
              ; Entries = Edges ),
              atom_string(L, Label), strings(Ps, PredLabels), strings(Ss, SuccLabels),
              strings(Reads, ReadNames), strings(Writes, WrittenNames),
              strings(Out, OutNames), strings(Keeps, KeepNames), strings(Outputs, OutputNames),
              Row = _{label:Label, predecessors:PredLabels, successors:SuccLabels,
                      reads:ReadNames, writes:WrittenNames, live_out:OutNames,
                      keeps:KeepNames, outputs:OutputNames, entries:Entries}
            ), Rows),
    json_write_dict(current_output, Rows, [width(0)]), nl.

strings(Atoms, Strings) :- maplist(atom_string, Atoms, Strings).
