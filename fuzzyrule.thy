theory fuzzyrule
  imports Main Complex_Main
begin

declare[[show_sorts]]

ML \<open>



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


datatype 'a Try_match_res = NoMatch | Matches | MightMatch of 'a
datatype 'a option = Some of 'a | None

(* returns the lambda var and lambda body to construct the match*)
fun try_match (a: cterm) (b: cterm) vIndex: (cterm*cterm) Try_match_res = 
 
  let 
    val _ = writeln ("try_match = " 
          ^  "  " ^  @{make_string} a 
          ^  " WITH " ^  @{make_string} b)
    val m = (Some (Thm.first_order_match (a, b))) handle Pattern.MATCH => None
    val _ = writeln ("first order match result = " ^  @{make_string} m)
    val result = 
      case m of
          Some _ => Matches
          | None => (
            case (Thm.term_of a, Thm.term_of b) of
            (_ $ _, _ $ _) => (
              let 
                val a_cf = Thm.dest_fun a
                val b_cf = Thm.dest_fun b
                val a_carg = Thm.dest_arg a
                val b_carg = Thm.dest_arg b
              in
                case try_match a_cf b_cf vIndex of
                 Matches => (
                  case try_match a_carg b_carg vIndex of
                    Matches => Matches
                  | MightMatch (v,b) => MightMatch (v, Thm.apply a_cf b)
                  | NoMatch => 
                      let val v: cterm = Thm.var (("x", 0), Thm.ctyp_of_cterm a_carg)
                      in MightMatch (v, Thm.apply a_cf v)
                      end)
                | MightMatch (v, b) => MightMatch (v, Thm.apply b  a_carg)
                | NoMatch =>  NoMatch
              end)
            | _ => 
                trace ("other case: " 
                    ^ "a = " ^ @{make_string} (Thm.term_of a) 
                    ^ "b = " ^ @{make_string} (Thm.term_of b) )
                NoMatch)
    val _ = writeln ("try_match = " 
          ^  " " ^ @{make_string} a 
          ^  " WITH " ^ @{make_string} b
          ^  " ==> " ^ @{make_string} result)
  in
     result
  end

fun remove_pure_prop (ct: cterm): cterm =
  case Thm.term_of ct of
   (Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"})) $ _ => remove_pure_prop (Thm.dest_arg ct)
   | (Const ("HOL.Trueprop", _) $ _) => remove_pure_prop (Thm.dest_arg ct)
   | _ => ct


fun find_back_subst_P (a: cterm) (b: cterm): cterm Try_match_res =
  case try_match (remove_pure_prop a) (remove_pure_prop b) 0 of
    MightMatch (v,b) => 
      let 
        val _ = writeln ("back_subst_P = " ^ @{make_string} v ^ " => " ^ @{make_string} b)
        val abs: cterm = Thm.lambda v b
      in
        MightMatch abs
      end
  | NoMatch => NoMatch
  | Matches => Matches

fun new_back_subst ctxt va vb = 
  let 
    val imp = Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"})
    val trueprop = (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}))
    val Q = Var (("Q", 0), @{typ "'a::type \<Rightarrow> 'b::type \<Rightarrow> bool"})
    val x = Var (("x", 1), @{typ "'a::type"})
    val x2 = Var (("x'",2), @{typ "'a::type"})
    val y = Var (("y",3), @{typ "'b::type"})
    val y2 = Var (("y'",4), @{typ "'b::type"})
    val eqa = Const ("HOL.eq", @{typ "'a::type \<Rightarrow> 'a::type \<Rightarrow> bool"})
    val eqb = Const ("HOL.eq", @{typ "'b::type \<Rightarrow> 'b::type \<Rightarrow> bool"})
    val t: term = imp $
     (trueprop $ (Q $ x $ y)) $
     (imp $
       (trueprop $ (eqa $ x $ x2)) $
       (imp $
         (trueprop $ (eqb $ y $ y2)) $
         (trueprop $ (Q $ x2 $ y2))))
  in 
    Thm.assume (Thm.cterm_of ctxt t)
  end
(* TODO instead generate \<And>Q x x' y y'.  ... then prove with stuff  *)


fun fuzzy_rule (ctxt: Proof.context) (rules: thm list) (facts: thm list) (i: int) (thm: thm) : thm Seq.seq = 
    let 
      val _ = trace ("fuzzy " 
                    ^ "\n ctxt: " ^ ( @{make_string}  ctxt ) 
                    ^ "\n rules: " ^ ( @{make_string} rules)
                    ^ "\n facts: " ^ ( @{make_string} facts)
                    ^ "\n i: " ^ ( @{make_string} i)
                    ^ "\n thm: " ^ ( @{make_string} thm)
                    ^ "\n thm concl: " ^ ( @{make_string} (Thm.cconcl_of thm))
                    ^ "\n thm prems: " ^ ( @{make_string} (Thm.cprems_of thm))

                 ) ()
      val subgoals = Thm.cprems_of thm
    in
    if i < 1 orelse i > length subgoals then trace "Warning: wrong subgoal index" Seq.empty
    else case rules of
     [rule] =>
      let 
        val _ = trace ("fuzzy rule:"
                    ^ "\n rule concl: " ^ ( @{make_string} (Thm.cconcl_of rule))
                    ^ "\n rule prems: " ^ ( @{make_string} (Thm.cprems_of rule))
                    ^ "\n rule prop: " ^ ( @{make_string} (Thm.cprop_of rule))
                    ^ "\n rule hyps: " ^ ( @{make_string} (Thm.chyps_of rule))
          ) ()
        val goal = nth (Thm.cprems_of thm) (i-1)
        val _ = writeln ("goal = " ^ @{make_string} goal)
        val m = find_back_subst_P goal (Thm.cconcl_of rule)
        val _ = writeln ("m = " ^ (@{make_string} m))
      in
      case m of
        Matches =>
          Tactic.resolve_tac ctxt rules i thm
      | NoMatch =>
          Seq.empty
      | MightMatch p =>
          let 
            val ptyp = Thm.ctyp_of_cterm p
            val ptyp_raw = Thm.typ_of ptyp
            val argtyp = Thm.dest_ctyp0 ptyp
            val back_subst = Thm.instantiate ([((("'a", 0), @{sort "type"}), argtyp) ], [((("P", 0), ptyp_raw), p )]) @{thm back_subst}
            val _ = writeln ("rule1: " ^ @{make_string} back_subst)
            val back_subst1: thm = new_back_subst ctxt "blub" "bla"
            val _ = writeln ("back_subst1: " ^ @{make_string} back_subst1)
            val back_subst2 = Thm.instantiate ([((("'a", 0), @{sort "type"}), argtyp) ], [((("P", 0), ptyp_raw), p )]) back_subst1
            val _ = writeln ("back_subst2: " ^ @{make_string} back_subst2)
          (* TODO rename schematic vars*)
          in
            Tactic.resolve_tac ctxt [back_subst] i thm
          end
      (*Seq.empty*)
      (*Tactical.ORELSE
      (Tactic.resolve_tac ctxt rules i,
       Tactic.resolve_tac ctxt [@{thm back_subst}] i) thm*)
      end
    | _ =>
      trace "Only one rule allowed for fuzzy_rule method"
      Seq.empty
    end


val _ = 
  Theory.setup
    (Method.setup \<^binding>\<open>fuzzy_rule\<close>
        (Attrib.thms  >> (fn rules => (fn ctxt => (METHOD (HEADGOAL o fuzzy_rule ctxt rules)))))
        "apply some intro/elim rule (potentially classical)")


\<close>

declare[[show_sorts]]
thm back_subst

ML \<open>
Thm.instantiate ([((("'a", 0), @{sort "type"}), @{ctyp "int"}) ], [((("P", 0), @{typ "int \<Rightarrow> bool"}), @{cterm "\<lambda>x::int. x < 0" } )]) @{thm back_subst}
\<close>

definition P :: "int \<Rightarrow> bool" where "P x \<equiv> True"

lemma xx: "P x" by (simp add: P_def)

ML \<open>Thm.concl_of  @{thm xx}\<close> 

ML \<open>
Thm.renamed_prop (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ (Const ("Scratch.P", @{typ "int \<Rightarrow> bool"}) $ Var (("x", 0), @{typ "int"}))) @{thm xx}
\<close> 

ML \<open>@{term "\<lbrakk>Q x y; x = x'; y = y'\<rbrakk> \<Longrightarrow> Q x' y'"}
\<close> 

ML \<open>
val tt= Thm.instantiate ([((("'a", 0), @{sort "type"}), @{ctyp "int"}) ], [((("P", 0), @{typ "int \<Rightarrow> bool"}), @{cterm "P"} )]) @{thm back_subst}
\<close> 






thm back_subst[where P="\<lambda>x. x > 5"]


locale example =
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes R: "\<And>a b c. a \<ge> 2 \<Longrightarrow> P (a*b) (a*c)"

declare[[rule_trace=true]]

lemma (in example) 
  assumes a: "4 > 2"
  shows "P 8 4"
  apply (fuzzy_rule R)
   apply (fuzzy_rule R)


 apply (rule back_subst[where P="\<lambda>x. P x 4"])
apply (fuzzy_rule R)

  oops

lemma 
  assumes a: "x + a = x"
  shows "Q (\<lambda>x. f x a)"
  apply (fuzzy_rule a)


lemma (in example) 
  assumes a: "4 > 2"
  shows "P (2*4) (2*2)"
  apply (fuzzy_rule R)
  oops


lemma (in example) 
  assumes a: "4 > 2"
  shows "P 8 4"
  apply (rule back_subst[where P="\<lambda>x. P 8 x"], rule back_subst[where b="8"], rule R) back 
proof -
  show "2 \<le> (2::int)"
    by simp
   apply_end auto
qed

  show "P (2*4) (2*2)"
    by (rule R, simp)
  show " 2 * 4 = (8::int)"
    by simp
  show " 2 * 2 = (4::int)"
    by simp
qed


lemma comm: "x+y = y+(x::int)"
  by simp

lemma "1+(2::int) = 2+1"
  apply (fuzzy_rule comm)

ML \<open>
writeln (@{make_string} @{cterm "1+1"});
writeln (@{make_string} (Thm.cprop_of @{thm comm}));
writeln (@{make_string} (Thm.first_order_match (@{cterm "2+1 = 1+(2::int)"}, Thm.cprop_of @{thm comm})))
\<close>


lemma (in example) 
  assumes a: "4 > 2"
  shows "P (2*4) (2*2)"
  using a apply (fuzzy_rule R)
  apply simp
  done


lemma (in example) 
  assumes a: "4 > 2"
  shows "P 8 4"
  using a apply (fuzzy_rule R)


lemma (in example) "P 8 4"
proof (fuzzy_rule R)  (* FAILS *)

  oops

lemma (in example) "P 8 4"
proof (rule R)  (* FAILS *)





end