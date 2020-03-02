section \<open>Fuzzy Goal Cases\<close>


theory fuzzy_goal_cases
imports Main
begin

text "Import this theory to use the fuzzy goal cases method.
The source code for the new method is implemented in the following ML file:"

ML_file "fuzzy_goal_cases.ML"


text "Here is a short example:"

definition "blub n \<equiv> n mod 2 = 0"

lemma "x = 42 \<longrightarrow> blub y \<longrightarrow> C"
proof (intro impI, fuzzy_goal_cases X )
  case X

  text "Now the assumptions from case X are available with kind of meaningful names: "

  have "x = 42" using X.x_def .
  have "blub y" using X.blub .

  oops

  text "The following test is for bound variables with De Bruijn indices."

lemma "(\<exists>blub f. blub = f 42 \<and> f = id \<and> (\<lambda>x y z. y) = g \<and> P blub) \<longrightarrow> C"
proof (intro impI, elim exE conjE, fuzzy_goal_cases X)
  case (X blub f)

  have "P blub" using X.P .
  have "f = id" using X.f_eq .
  have "blub = f 42" using X.blub_eq .
  have "(\<lambda>x y z. y) = g" using X.y_eq .

  oops


end