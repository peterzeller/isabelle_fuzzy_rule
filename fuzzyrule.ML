


datatype ('a,'subst) Try_match_res = 
    NoMatch 
  | Matches of 'subst 
  | MightMatch of 'a


(* a first-order substitution of types and terms *)
type fo_subst = (((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list )

fun contains_var (t: term) v: bool = 
  case t of
    (f $ a) => contains_var f v orelse contains_var a v
  | Abs(_,_,b) => contains_var b v
  | Var v' => v = v'
  | _ => false

fun starts_with_var (t: term): (indexname * typ) option =
  case t of
    (f $ a) => 
      (case starts_with_var f of 
          SOME v => if contains_var a v then NONE else SOME v
        | NONE => NONE)
  | Var v => SOME v 
  | _ => NONE

fun try_first_order_match (a: cterm) (b: cterm): fo_subst option =
  (SOME (Thm.first_order_match (b, a))) 
    handle Pattern.MATCH => 
    (case starts_with_var (Thm.term_of a) of
       SOME _ => SOME ([], []) (* TODO produce real substitution *)
     | NONE => NONE)

fun orelse_try f opt =
  case opt of SOME _ => opt | NONE => f ()

(* tries to first-order match in both directions, giving an existing substitution.*)
fun try_first_order_match_bidirectional (a: cterm) (b: cterm) (subst: fo_subst): fo_subst option =
  let 
    val a: cterm = Thm.instantiate_cterm subst a
    val b: cterm = Thm.instantiate_cterm subst b
  in
    try_first_order_match a b 
    |> orelse_try (fn () => try_first_order_match b a)
  end

(* returns the lambda var and lambda body to construct the match*)
fun try_match ctxt (a: cterm) (b: cterm) substI vIndex (depVars: cterm list): (cterm*cterm, ((indexname * sort) * ctyp) list *
    ((indexname * typ) * cterm) list) Try_match_res = 
 
  let 
    val m = try_first_order_match_bidirectional a b substI
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
                case try_match ctxt a_cf b_cf substI vIndex depVars of
                 Matches subst => 
                  let 
                  in
                  case try_match ctxt a_carg b_carg subst vIndex depVars of
                    Matches subst => Matches subst
                  | MightMatch (v,b) => MightMatch (v, Thm.apply a_cf b)
                  | NoMatch => 
                      let 
                        val t: typ = List.foldl (fn (depVar, rt) => Thm.typ_of_cterm depVar --> rt) (Thm.typ_of_cterm a_carg) depVars
                        val ct: ctyp = Thm.ctyp_of ctxt t
                        val v: cterm = Thm.var (("x", 1+vIndex), ct)
                        val dv: cterm = List.foldl (fn (depVar, x) => Thm.apply x depVar ) v depVars
                            (* (('a * 'b) -> 'b) -> 'b -> 'a list -> 'b *)
                      in MightMatch (v, Thm.apply a_cf dv)
                      end
                  end
                | MightMatch (v, b) => MightMatch (v, Thm.apply b  a_carg)
                | NoMatch =>  NoMatch
              end)
            | (Abs(a_x, a_t, a_b), Abs(b_x, b_t, b_b)) =>
               let 
                val (a_cx, a_cb) = Thm.dest_abs (SOME "x") a
                val (b_cx, b_cb) = Thm.dest_abs (SOME "x") b
               in
                case try_match ctxt a_cb b_cb substI vIndex (a_cx::depVars) of
                  Matches subst => Matches subst (* TODO need to quantify? *)
                | MightMatch (v,b) =>
                    MightMatch (v, Thm.lambda a_cx b)
                | NoMatch => NoMatch
               end
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
fun find_back_subst_P ctxt (a: cterm) (b: cterm): (cterm,unit) Try_match_res =
  case try_match ctxt (remove_pure_prop a) (remove_pure_prop b) ([],[]) 0 [] of
    MightMatch (v,body) => 
      let 
        val abs: cterm = Thm.lambda v body
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
    val m = find_back_subst_P ctxt goal (Thm.cconcl_of rule)
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
    let
      fun continue i newthm =
        let
          val new_subgoals = length (Thm.cprems_of newthm) - length (Thm.cprems_of thm)
          val new_goal_idxs = (take (i-1) goal_idxs) @ (map (fn i => i + new_subgoals) (drop (i) goal_idxs))
        in
          resolve_with_facts ctxt fs newthm new_goal_idxs
        end
      val goal_idxs_seq = Seq.of_list goal_idxs
    in
      Seq.append 
        (goal_idxs_seq |> Seq.maps (fn i => Tactic.resolve_tac ctxt [f] i thm |> Seq.maps (continue i)))
        (goal_idxs_seq |> Seq.maps (fn i => fuzzy_rule ctxt [f] [] i thm      |> Seq.maps (continue i)))
    end
      
and fuzzy_rule (ctxt: Proof.context) (rules: thm list) (facts: thm list) (i: int) (thm: thm) : thm Seq.seq = 
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
        "apply some intro/elim rule with fuzzy matching");


(* fuzzy cases*)

(*

fun fuzzy_goal_cases_tac case_names : context_tactic =
  fn (ctxt, st) =>
    let
      val cases =
        (if null case_names then map string_of_int (1 upto Thm.nprems_of st) else case_names)
        |> map (rpair [] o rpair [])
        |> Rule_Cases.make_common ctxt (Thm.prop_of (Rule_Cases.internalize_params st));
    in CONTEXT_CASES cases all_tac (ctxt, st) end;

val _ =
  Theory.setup 
  (Method.setup \<^binding>\<open>fuzzy_goal_cases\<close> (Scan.lift (Scan.repeat Args.name_token) >> (fn names => fn _ =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      (case drop (Thm.nprems_of st) names of
        [] => NONE
      | bad =>
          if detect_closure_state st then NONE
          else
            SOME (fn () => ("Excessive case name(s): " ^ commas_quote (map Token.content_of bad) ^
              Position.here (#1 (Token.range_of bad)))))
      |> (fn SOME msg => Seq.single (Seq.Error msg)
           | NONE => fuzzy_goal_cases_tac (map Token.content_of names) (ctxt, st))))))

*)
