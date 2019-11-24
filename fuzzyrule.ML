


datatype ('a,'subst) Try_match_res = 
    NoMatch 
  | Matches of 'subst 
  | MightMatch of 'a


(* a first-order substitution of types and terms *)
type fo_subst = (((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list )

(* tries to first-order match in both directions, giving an existing substitution.*)
fun try_first_order_match (a: cterm) (b: cterm) (subst: fo_subst): fo_subst option =
  let 
    val a: cterm = Thm.instantiate_cterm subst a
    val b: cterm = Thm.instantiate_cterm subst b
  in
    (SOME (Thm.first_order_match (b, a))) 
    handle Pattern.MATCH => 
    ((SOME (Thm.first_order_match (a, b))) 
    handle Pattern.MATCH => NONE)
  end

(* returns the lambda var and lambda body to construct the match*)
fun try_match (a: cterm) (b: cterm) subst vIndex: (cterm*cterm, ((indexname * sort) * ctyp) list *
    ((indexname * typ) * cterm) list) Try_match_res = 
 
  let 
    val m = try_first_order_match a b subst
    val result = 
      case m of
          SOME subst => Matches subst (* TODO use subst*)
          | NONE => (
            case (Thm.term_of a, Thm.term_of b) of
            (_ $ _, _ $ _) => (
              let 
                val a_cf = Thm.dest_fun a
                val b_cf = Thm.dest_fun b
                val a_carg = Thm.dest_arg a
                val b_carg = Thm.dest_arg b
              in
                case try_match a_cf b_cf subst vIndex of
                 Matches subst => 
                  let 
                  in
                  case try_match a_carg b_carg subst vIndex of
                    Matches subst => Matches subst
                  | MightMatch (v,b) => MightMatch (v, Thm.apply a_cf b)
                  | NoMatch => 
                      let val v: cterm = Thm.var (("x", 0), Thm.ctyp_of_cterm a_carg)
                      in MightMatch (v, Thm.apply a_cf v)
                      end
                  end
                | MightMatch (v, b) => MightMatch (v, Thm.apply b  a_carg)
                | NoMatch =>  NoMatch
              end)
            | _ => NoMatch)
  in
     result
  end

(* removes Pure.prop and HOL.Trueprop from a cterm *)
fun remove_pure_prop (ct: cterm): cterm =
  case Thm.term_of ct of
   (Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"})) $ _ => remove_pure_prop (Thm.dest_arg ct)
   | (Const ("HOL.Trueprop", _) $ _) => remove_pure_prop (Thm.dest_arg ct)
   | _ => ct

(* find an instantiation for the predicate in the back_subst theorem, 
  such that goal a and b are made (more) equal. *)
fun find_back_subst_P (a: cterm) (b: cterm): (cterm,unit) Try_match_res =
  case try_match (remove_pure_prop a) (remove_pure_prop b) ([],[]) 0 of
    MightMatch (v,b) => 
      let 
        val abs: cterm = Thm.lambda v b
      in
        MightMatch abs
      end
  | NoMatch => NoMatch
  | Matches _ => Matches ()


fun max x y = if x < y then y else x

fun maxidx_of_terms terms =
  List.foldl (uncurry max) ~1 (map maxidx_of_term terms)

fun maxidx_of_thm thm =
  max (maxidx_of_term (Thm.concl_of thm)) (maxidx_of_terms (Thm.prems_of thm))

fun maxidx_of_thms thms =
  List.foldl (uncurry max) ~1 (map maxidx_of_thm thms)

(* one step of fuzzy_rule back_subst application *)
fun fuzzy_rule_step ctxt maxidx rule iteration i thm : ((thm * int) Seq.seq) = 
  let 
    val goal = nth (Thm.cprems_of thm) (i-1)
    val m = find_back_subst_P goal (Thm.cconcl_of rule)
  in
  case m of
    Matches () =>
      (* if the goal matches with the rule, use normal resolve_tac *)
      (Tactic.resolve_tac ctxt [rule] i thm) |> Seq.map (fn t => (t, iteration))
  | NoMatch =>
      (* if there is no possible first-order match, return no results *)
      Seq.empty
  | MightMatch p =>
      (* if we can make the terms equal using theorem back_subst with predicate p, then try to apply it: *)
      let 
        val maxIndex = max maxidx (maxidx_of_thms ([thm, rule]))
        val ptyp = Thm.ctyp_of_cterm p
        val ptyp_raw = Thm.typ_of ptyp
        val argtyp = Thm.dest_ctyp0 ptyp
        val argtyp_raw = Thm.typ_of argtyp
        val vname: string = "y"
        val v = Thm.cterm_of ctxt (Var ((vname,maxIndex + 1), argtyp_raw))
        val back_subst = Thm.instantiate ([((("'a", 0), @{sort "type"}), argtyp) ], 
              [((("P", 0), ptyp_raw), p ), 
               ((("a", 0), argtyp_raw), v)]) 
              @{thm back_subst}
        val newThms = Tactic.resolve_tac ctxt [back_subst] i thm
      in
        Seq.maps (fn(thm) => fuzzy_rule_step ctxt maxidx rule (iteration+1) i thm) newThms
      end
  end


fun range start count =
  if count <= 0 then [] else start :: range (start+1) (count-1)

(* tries to resolve the subgoals with index from goal_idxs in thm using the facts. 
   Works from left to right. *)
fun resolve_with_facts ctxt (facts: thm list) (thm: thm) (goal_idxs: int list): thm Seq.seq =
  case facts of 
  [] => Seq.single thm
  | (f:: fs) =>
    goal_idxs
    |> Seq.of_list
    |> Seq.maps (fn i => 
      Tactic.resolve_tac ctxt [f] i thm
      |> Seq.maps (fn newthm =>
          let
            val new_subgoals = length (Thm.cprems_of newthm) - length (Thm.cprems_of thm)
            val new_goal_idxs = (take (i-1) goal_idxs) @ (map (fn i => i + new_subgoals) (drop (i) goal_idxs))
          in
            resolve_with_facts ctxt fs newthm new_goal_idxs
          end))
      

fun fuzzy_rule (ctxt: Proof.context) (rules: thm list) (facts: thm list) (i: int) (thm: thm) : thm Seq.seq = 
    let 
      val subgoals = Thm.cprems_of thm
    in
    if i < 1 orelse i > length subgoals then Seq.empty (* focus on nonexistant subgoal *)
    else
     Seq.of_list rules
     |> Seq.maps (fn rule =>
      let 
        val maxidx = maxidx_of_thms ([thm] @ rules @ facts)
        val res_thms = fuzzy_rule_step ctxt maxidx rule 0 i thm
      in
        res_thms |> Seq.maps (fn (res_thm, _) =>
          let 
            val newSubgoals = Thm.cprems_of res_thm
            val subgoal_count = 1 + length newSubgoals - length subgoals
          in
            resolve_with_facts ctxt facts res_thm (range i subgoal_count)
          end
        )
      end)
    end


val _ = 
  Theory.setup
    (Method.setup \<^binding>\<open>fuzzy_rule\<close>
        (Attrib.thms  >> (fn rules => (fn ctxt => (METHOD (HEADGOAL o fuzzy_rule ctxt rules)))))
        "apply some intro/elim rule with fuzzy matching")

