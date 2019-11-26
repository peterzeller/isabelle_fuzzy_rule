section \<open>Fuzzy Rule Examples\<close>

theory fuzzyrule_examples
  imports fuzzyrule
begin

text \<open>The method @{method fuzzy_rule} works similar to @{method rule} but is more flexible in its application.\<close>

text \<open>For instance, the rule R in the following example cannot be applied with @{method rule}
as @{term "8::int"} does not match the pattern @{term "a*b"}.  \<close>

lemma 
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes R: "\<And>a b c. a \<ge> 2 \<Longrightarrow> P (a*b) (a*c)"
  shows "P 8 4"
  apply (fuzzy_rule R)

  text \<open>With @{method fuzzy_rule}, new schematic variables and subgoals for proving the necessary equalities
are automatically introduced, giving the following subgoals: 

@{subgoals}


These subgoals can then be discharged automatically:\<close>

    by auto

  text \<open>This also works when a variable appears multiple times in a rule:\<close>


lemma 
  fixes P :: "int \<Rightarrow> int \<Rightarrow> bool"
  assumes rr: "\<And>x. P x x"
  shows "P (3*4) (4*3)"
  apply (fuzzy_rule rr)

  text \<open> Here we get the following subgoal:  

@{subgoals}

\<close>

  by auto

text "The method @{method fuzzy_rule} is also more flexible in the use of facts.
While @{method rule} requires all facts to be given in the correct order, 
with @{method fuzzy_rule} the order only determines a priority, but does not affect the set of results.
Therefore the following application of the transitivity rule works, even though the facts @{term a} 
and @{term b} are given in the wrong order:  "


lemma 
  fixes x y z :: int
  assumes a: "x \<le> y" and b: "y \<le> z"
    and q: Q and r: R
  shows "x \<le> z"
  using b a by (fuzzy_rule order.trans)

text "The following example tests that the rule does not interfere with other subgoals: "

lemma 
  fixes x y z :: int
  assumes a: "Q \<Longrightarrow> x \<le> y" and b: "R \<Longrightarrow> y \<le> z"
    and q: Q and r: R
  shows "x \<le> z \<and> x \<le> y \<and> y \<le> z"
  apply (intro conjI)
  using b a apply (fuzzy_rule order.trans)
proof -
  show Q using q . 
  show R using r .
  show "x \<le> y" using a q by auto
  show "y \<le> z" using b r by auto
qed


text "The facts are first applied with normal rule application, but if this is not successful
  we try to apply @{method fuzzy_rule} recursively, so that they do not have to match exactly."

lemma 
  assumes a: "\<And>a b. P (a,b)"
    and f_def: "\<And>a b. f a b = (a,b)"
    and r: "\<And>a b. \<lbrakk>P (f a b)\<rbrakk> \<Longrightarrow> Q (a,b) y"
  shows "Q x y"
  using a proof (fuzzy_rule r)
  show "(fst x, snd x) = x" by force
  show "(fst x, snd x) = f (fst x) (snd x)" unfolding f_def ..
qed

subsection "Future Work"

text "In a future version, matching should also work for lambda instructions as in the following example:"

lemma 
  shows "(SOME x::int. x \<ge> 5 \<and> x < 7 \<and> x mod 2 = 1) = 5"
  apply (fuzzy_rule someI)
  oops



  text "Additionally, it would be nice to have a similar fuzzy alternative for the @{method subst} method."




end