theory fuzzyrule_examples
  imports fuzzyrule
begin

text "Fuzzy Rule Examples"

text "The method @{method fuzzy_rule} works similar to @{method rule} but "

lemma 
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes R: "\<And>a b c. a \<ge> 2 \<Longrightarrow> P (a*b) (a*c)"
  shows "P 8 4"
  apply (fuzzy_rule R)
    apply auto
  done

proof (fuzzy_rule R)



lemma 
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes rr: "\<And>x. P x x"
  shows "P (3*4) (4*3)"
  apply (fuzzy_rule rr)
   apply auto
  done



lemma 
  fixes x y z :: int
  assumes a: "Q \<Longrightarrow> x \<le> y" and b: "R \<Longrightarrow> y \<le> z"
  shows "x \<le> z \<and> x \<le> y \<and> y \<le> z"
  apply (intro conjI)
(*  using b a  apply (rule order.trans) *)
  using b a apply (fuzzy_rule order.trans)
  using a b  apply auto
  done



thm back_subst[where P="\<lambda>x. x > 5"]


lemma 
  shows "(SOME x::int. x \<ge> 5 \<and> x < 6) = 5"
  apply (fuzzy_rule someI[where P="\<lambda>x::int. x = 5"])
   apply auto
  done



locale example =
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes R: "\<And>a b c. a \<ge> 2 \<Longrightarrow> P (a*b) (a*c)"

declare[[rule_trace=true]]

lemma (in example) 
  assumes a: "4 > 2"
shows "P 8 4"
  apply (fuzzy_rule R)
    apply auto
  done

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