


fun trace msg s =
  let val _ = writeln msg in s end


(*
THM:
  val hyps_of: thm -> term list
  val prop_of: thm -> term
*)

(*
 a = "Q (\<lambda>x. f x a)"
 b = "Q (\<lambda>x. f x a)"
 at = Const ("Pure.prop", "prop \<Rightarrow> prop") $
        (Const ("HOL.Trueprop", "bool \<Rightarrow> prop") $
          (Free ("Q", "('a \<Rightarrow> 'b) \<Rightarrow> bool") $ Abs ("x", "'a", Free ("f", "'a \<Rightarrow> 'c \<Rightarrow> 'b") $ Bound 0 $ Free ("a", "'c"))))
 bt = Const ("HOL.Trueprop", "bool \<Rightarrow> prop") $
        (Free ("Q", "('a \<Rightarrow> 'b) \<Rightarrow> bool") $ Abs ("x", "'a", Free ("f", "'a \<Rightarrow> 'c \<Rightarrow> 'b") $ Bound 0 $ Free ("a", "'c"))) 

*)


datatype ('a,'subst) Try_match_res = 
    NoMatch 
  | Matches of 'subst 
  | MightMatch of 'a



type fo_subst = (((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list )

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
    val _ = writeln (
             "try_match " ^  @{make_string} a 
          ^  "\n     WITH " ^  @{make_string} b)
    val m = try_first_order_match a b subst
    val _ = writeln ("first order match result = " ^  @{make_string} m)
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
            | _ => 
                trace ("other case: " 
                    ^ "a = " ^ @{make_string} (Thm.term_of a) 
                    ^ "b = " ^ @{make_string} (Thm.term_of b) )
                NoMatch)
    val _ = writeln (
             " try_match " ^ @{make_string} a 
          ^  "\n WITH " ^ @{make_string} b
          ^  "\n ==> " ^ @{make_string} result)
  in
     result
  end

fun remove_pure_prop (ct: cterm): cterm =
  case Thm.term_of ct of
   (Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"})) $ _ => remove_pure_prop (Thm.dest_arg ct)
   | (Const ("HOL.Trueprop", _) $ _) => remove_pure_prop (Thm.dest_arg ct)
   | _ => ct


fun find_back_subst_P (a: cterm) (b: cterm): (cterm,unit) Try_match_res =
  case try_match (remove_pure_prop a) (remove_pure_prop b) ([],[]) 0 of
    MightMatch (v,b) => 
      let 
        val _ = writeln ("back_subst_P = " ^ @{make_string} v ^ " => " ^ @{make_string} b)
        val abs: cterm = Thm.lambda v b
      in
        MightMatch abs
      end
  | NoMatch => NoMatch
  | Matches _ => Matches ()

fun new_back_subst ctxt (a_t: typ) (vP: string) (vx: string) (vy: string): thm = 
  let 
    val imp = Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"})
    val trueprop = (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}))
    val Q = Bound 2
    val x = Bound 1
    val x2 = Bound 0
    val eqa = Const ("HOL.eq", a_t --> a_t --> @{typ "bool"})
    val t_prop = @{typ "prop"}
    fun all s t b = Const ("Pure.all", (t --> t_prop) --> t_prop) $ Abs (s, t, b)

(* Const ("Pure.all", "('a::type \<Rightarrow> prop) \<Rightarrow> prop") $
     Abs ("x", "'a::type",
       Const ("Pure.all", "('b::type \<Rightarrow> prop) \<Rightarrow> prop") $
         Abs ("y", "'b::type",
*)

    val t: term = 
     all vP (a_t --> @{typ "bool"})  ( all vx a_t (all vy a_t ( 
     imp $ (trueprop $ (Q $ x2)) $
     (imp $
       (trueprop $ (eqa $ x2 $ x)) $
       (trueprop $ (Q $ x))))))
    val athm = Assumption.assume ctxt (Thm.cterm_of ctxt t)
    val thm2 = Tactic.resolve_tac ctxt [@{thm back_subst}] 1 athm
    val _ = writeln ("thm 2 = " ^ (@{make_string} (Seq.list_of thm2)))
    val thm3 = Assumption.export true ctxt ctxt (Seq.hd thm2)
    val _ = writeln ("thm 3 = " ^ (@{make_string} thm3))
  in 
    thm3
  end
(* TODO instead generate \<And>Q x x' y y'.  ... then prove with stuff  *)

fun max x y = if x < y then y else x

fun maxidx_of_terms terms =
  List.foldl (uncurry max) ~1 (map maxidx_of_term terms)

fun maxidx_of_thm thm =
  max (maxidx_of_term (Thm.concl_of thm)) (maxidx_of_terms (Thm.prems_of thm))


fun maxidx_of_thms thms =
  List.foldl (uncurry max) ~1 (map maxidx_of_thm thms)

fun fuzzy_rule_step ctxt maxidx rule iteration i thm : ((thm * int) Seq.seq) = 
  if iteration > 20 then Seq.empty
  else
  let 
    val goal = nth (Thm.cprems_of thm) (i-1)
    val _ = writeln ("fuzzy rule:"
                ^ "\n rule: " ^ ( @{make_string} rule)
                ^ "\n goal: " ^ ( @{make_string} goal)
      ) 
    val m = find_back_subst_P goal (Thm.cconcl_of rule)
    val _ = writeln ("m = " ^ (@{make_string} m))
  in
  case m of
    Matches () =>
      (Tactic.resolve_tac ctxt [rule] i thm) |> Seq.map (fn t => (t, iteration))
  | NoMatch =>
      Seq.empty
  | MightMatch p =>
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
        val _ = writeln ("rule1: " ^ @{make_string} back_subst)
        val newThms = Tactic.resolve_tac ctxt [back_subst] i thm
      in
        Seq.maps (fn(thm) => fuzzy_rule_step ctxt maxidx rule (iteration+1) i thm) newThms
      end
  end

fun seq_range (start: int) (count: int): int Seq.seq =
  Seq.make (fn () =>   
    if count <= 0 then NONE
    else SOME (start, seq_range (start+1) (count-1)))

fun range start count =
  if count <= 0 then [] else start :: range (start+1) (count-1)

fun resolve_with_facts ctxt (facts: thm list) (thm: thm) (goal_idxs: int list): thm Seq.seq =
  case facts of 
  [] => Seq.single thm
  | (f:: fs) =>
    let
      val subgoals = Thm.cprems_of thm
      val _ = writeln ("subgoals = " ^ @{make_string} subgoals)
      val _ = writeln (" goal_idxs = " ^ @{make_string} goal_idxs)  
    in
    goal_idxs
    |> Seq.of_list
    |> Seq.maps (fn i => 
      Tactic.resolve_tac ctxt [f] i thm
      |> Seq.maps (fn newthm =>
          let
            val new_subgoals = length (Thm.cprems_of newthm) - length (Thm.cprems_of thm)
            val new_goal_idxs: int list = (take (i-1) goal_idxs) @ (map (fn i => i + new_subgoals) (drop (i) goal_idxs))
          in
               resolve_with_facts ctxt fs newthm new_goal_idxs
          end))
      
    end

fun fuzzy_rule (ctxt: Proof.context) (rules: thm list) (facts: thm list) (i: int) (thm: thm) : thm Seq.seq = 
    let 
      val subgoals = Thm.cprems_of thm
    in
    if i < 1 orelse i > length subgoals then trace "Warning: wrong subgoal index" Seq.empty
    else
     Seq.of_list rules
     |> Seq.maps (fn rule =>
      let 
        val maxidx = maxidx_of_thms ([thm] @ rules @ facts)
        val res_thms = fuzzy_rule_step ctxt maxidx rule 0 i thm
      in
        res_thms |> Seq.maps (fn (res_thm, eqs) =>
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
        "apply some intro/elim rule (potentially classical)")

