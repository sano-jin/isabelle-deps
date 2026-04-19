chapter\<open>An example demonstrating the use of structural induction.\<close>

theory InductTest
imports Main begin

type_synonym var = nat

datatype exp =
  Var var
| App exp exp
| Lam exp


text \<open>
Free variables of an expression.
The constructor Lam binds (hides) the variable with index 0 in its subexpression,
and all other free variables are shifted down by one.
\<close>
primrec FV :: "exp => var set"
where
  "FV (Var var) = {var}"
| "FV (App e1 e2) = FV e1 \<union> FV e2"
| "FV (Lam e) = {n. Suc n \<in> FV e}"


text \<open>
Free-variable replacement.
This operation is designed so that bound variables remain unchanged.
\<close>
primrec
  vmap :: "(var => var) => exp => exp"
where
  "vmap f (Var var) = Var (f var)"
| "vmap f (App e1 e2) = App (vmap f e1) (vmap f e2)"
| "vmap f (Lam e) = Lam (vmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) e)"


text \<open>
Main theorem (to be proven later):

\<^item> If @{term "0 \<notin> FV exp"}, then
\<^item> @{term "vmap Suc (vmap (\<lambda>x. x - 1) exp) = exp"}.

If 0 is not among the free variables of an expression,
then shifting all variables down and then up again
does not change the expression.

We now proceed with several auxiliary lemmas.
\<close>


text \<open>
Composition of free-variable replacements.
\<close>
lemma vmap_compose:
  "vmap f (vmap g exp) = vmap (f \<circ> g) exp"
proof (induct exp arbitrary: f g)
  case (Var var)
  then show ?case
    by auto
next
  case (App exp1 exp2)
  then show ?case
    by auto
next
  case (Lam exp)
  have P2: "(\<lambda>x. if x = 0 then x else f (x - 1) + 1) \<circ>
    (\<lambda>x. if x = 0 then x else g (x - 1) + 1) =
    (\<lambda>x. if x = 0 then x else f (g (x - 1)) + 1)"
    using Suc_eq_plus1 Zero_not_Suc diff_Suc_1 by auto
  show ?case
    apply auto
    using Lam P2 by presburger
qed


text \<open>
A helper lemma.
\<close>
lemma helper_lemma_for_the_generalised_lemma:
  assumes "\<forall>x \<in> FV (Lam exp). (k <= x --> n <= x)"
  shows "\<forall>x \<in> FV exp. (k + 1 <= x --> n + 1 <= x)"
using assms
apply auto
using Suc_le_D by auto


text \<open>
A generalised lemma used to prove the next result.
\<close>
lemma generalised_lemma_for_shift_down_and_up:
  assumes "\<forall>x \<in> FV exp. (k <= x --> n <= x)"
  shows "vmap (\<lambda>x. if k <= x then x - n + n else x) exp = exp"
using assms
proof (induct exp arbitrary: n k)
  case (Var var)
  then show ?case
    apply auto
    done
next
  case (App exp1 exp2)
  then show ?case
    apply auto
    done
next
  case (Lam exp)
  then have H: "\<forall>x \<in> FV exp. (k + 1 \<le> x --> n + 1 \<le> x)"
    using helper_lemma_for_the_generalised_lemma by blast
  have f: "\<forall>x.
    (if x = 0 then x else (if k \<le> x - 1 then x - 1 - n + n else x - 1) + 1) =
    (if (k + 1) \<le> x then x - (n + 1) + (n + 1) else x)"
    by auto
  then show ?case
    apply auto
    using H Lam.hyps Suc_eq_plus1 by presburger
qed


text \<open>
A slightly more general lemma used to prove the final theorem.
\<close>
lemma shift_down_and_up_if_less_than_n_notin:
  assumes "\<forall>x \<in> FV exp. n <= x"
  shows "vmap (\<lambda>x. x - n + n) exp = exp"
proof -
  have "\<forall>x \<in> FV exp. (0 <= x --> n <= x)"
    by (simp add: assms)
  then have "vmap (\<lambda>x. if 0 <= x then x - n + n else x) exp = exp"
    using generalised_lemma_for_shift_down_and_up by blast
  then have "vmap (\<lambda>x. x - n + n) exp = exp"
    by simp
  then show ?thesis .
qed


text \<open>
The main theorem.
If 0 is not among the free variables of an expression,
then shifting all variables down and then up again
does not change the expression.
\<close>
theorem shift_down_and_up_if_0_notin:
  assumes "0 \<notin> FV exp"
  shows "vmap Suc (vmap (\<lambda>x. x - 1) exp) = exp"
proof -
  have "\<forall>x \<in> FV exp. 1 <= x"
    using assms not_less_eq_eq by auto
  then have "vmap (\<lambda>x. x - 1 + 1) exp = exp"
    using shift_down_and_up_if_less_than_n_notin by blast
  then have "vmap ((\<lambda>x. x + 1) \<circ> (\<lambda>x. x - 1)) exp = exp"
    by (simp add: comp_def)
  then have "vmap (\<lambda>x. x + 1) (vmap (\<lambda>x. x - 1) exp) = exp"
    by (simp add: vmap_compose)
  then show ?thesis
    by simp
qed

end

