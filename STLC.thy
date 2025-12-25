(*  Title:      STLC.thy
    Author:     Jin Sano
    Based on
    - HOL/Proofs/Lambda/Lambda.thy
      - Author:    Tobias Nipkow
      - Copyright  1995 TU Muenchen
    - HOL/Proofs/Lambda/LambdaType.thy
      - Author:    Stefan Berghofer
      - Copyright  2000 TU Muenchen
*)


section \<open>Basic definitions of Lambda-calculus\<close>


theory STLC
imports Main
begin


declare [[syntax_ambiguity_warning = false]]


subsection \<open>Lambda-terms in de Bruijn notation and substitution\<close>


(* De Bruijn-style lambda-terms.
   - Var n : a variable represented by a natural number (de Bruijn index).
   - App e1 e2 : application (written e_1 \cdot e_2).
   - Abs t e : abstraction $(\lambda t. e)$, which binds one variable.
   - Val n s : a constructor for base-type values of sort s. *)
datatype 'ty exp =
    Var nat
  | App "'ty exp" "'ty exp" (infixl \<open>\<cdot>\<close> 200)
  | Abs 'ty "'ty exp"
  | Val nat nat


(* The lifting operation "lift t k" shifts free variables in t that are >= k by 1.
   This is used when we move under a binder (to avoid variable capture). *)
primrec
  lift :: "['ty exp, nat] => 'ty exp"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
       (* Shift indices i >= k. *)
  | "lift (e1 \<cdot> e2) k = lift e1 k \<cdot> lift e2 k"
  | "lift (Abs \<tau> e) k = Abs \<tau> (lift e (k + 1))"
       (* Entering a binder raises cutoff. *)
  | "lift (Val v s) k = Val v s"


(* Capture-avoiding substitution "e'[e/i]": replace variable i in e' with e.
   - Variables above k are decremented (indices slide down).
   - At a binder (Abs), we lift s and substitute at k+1 to account for the new binder. *)
primrec
  subst :: "['ty exp, 'ty exp, nat] => 'ty exp"  (\<open>_[_'/_]\<close> [300, 0, 0] 300)
where
    subst_Var: "(Var j)[e/i] =
      (if i < j then Var (j - 1) else if j = i then e else Var j)"
  | subst_App: "(e1 \<cdot> e2)[e/i] = e1[e/i] \<cdot> e2[e/i]"
  | subst_Abs: "(Abs \<tau> e1)[e/i] = Abs \<tau> (e1[lift e 0 / i+1])"
  | subst_Val: "(Val v s)[e/i] = Val v s"


(* Do not use subst_Var as a default simp rule (prevents unwanted rewrites on variables). *)
declare subst_Var [simp del]


(* Prefer these simp facts to normalize conditionals/inequalities in goals. *)
declare if_not_P [simp] not_less_eq [simp]
  \<comment> \<open>don't add \<open>r_into_rtrancl[intro!]\<close>\<close>


subsection \<open>Call-By-Value Reduction\<close>


(* Values are exactly abstractions and base-type literals. *)
inductive is_val :: "'ty exp \<Rightarrow> bool" where
  v_abs [intro!]: "is_val (Abs \<tau> e)"
| v_nat [intro!]: "is_val (Val v s)"


(* Call-by-value small-step relation.
   - beta_v: Perform beta only when the argument is already a value.
   - appL: Evaluate the function part first (left-to-right).
   - appR: Then evaluate the argument.
   No reduction happens inside an abstraction. *)
inductive cbv :: "'ty exp \<Rightarrow> 'ty exp \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>v" 50) where
  beta_v [simp, intro]:
    "is_val v \<Longrightarrow>
     Abs \<tau> e \<cdot> v \<rightarrow>\<^sub>v e[v/0]"
| appL   [simp, intro]:
    "e1 \<rightarrow>\<^sub>v e1' \<Longrightarrow>
     e1 \<cdot> e2 \<rightarrow>\<^sub>v e1' \<cdot> e2"
| appR   [simp, intro]:
    "is_val v \<Longrightarrow>
     e \<rightarrow>\<^sub>v e' \<Longrightarrow>
     v \<cdot> e \<rightarrow>\<^sub>v v \<cdot> e'"


(* Inversion rules for the step relation. *)
inductive_cases cbv_cases [elim!]:
  "Var i \<rightarrow>\<^sub>v e"
  "Abs \<tau> e1 \<rightarrow>\<^sub>v e"
  "e1 \<cdot> e2 \<rightarrow>\<^sub>v e"
  "Val v s \<rightarrow>\<^sub>v e"


(* Zero or more reductions. *)
abbreviation cbv_star ::
  "'ty exp \<Rightarrow> 'ty exp \<Rightarrow> bool"
  (infixl "\<rightarrow>\<^sub>v\<^sup>*" 50) where
  "cbv_star \<equiv> rtranclp cbv"


subsection \<open>Some examples\<close>


lemma "is_val (Abs \<tau>1 (Var 0))"
  by (simp add: v_abs)


lemma "(Abs \<tau>1 (Var 0)) \<cdot> Val 0 0 \<rightarrow>\<^sub>v Val 0 0"
  by (metis beta_v is_val.simps less_irrefl subst_Var)


lemma "(Abs \<tau>1 (Var 0 \<cdot> Val 1 2)) \<cdot> (Abs \<tau>2 (Var 0)) \<rightarrow>\<^sub>v\<^sup>* Val 1 2"
proof -
  have P2: "(Var 0 \<cdot> Val 1 2)[(Abs \<tau>2 (Var 0))/0] = ((Abs \<tau>2 (Var 0)) \<cdot> Val 1 2)"
    by (simp add: subst_Var)

  have P3: "(Abs \<tau>1 (Var 0 \<cdot> Val 1 2)) \<cdot> (Abs \<tau>2 (Var 0)) \<rightarrow>\<^sub>v
        ((Abs \<tau>2 (Var 0)) \<cdot> Val 1 2)"
    by (metis P2 beta_v v_abs)

  have P4: "((Abs \<tau>2 (Var 0)) \<cdot> Val 1 2) \<rightarrow>\<^sub>v Val 1 2"
    by (metis beta_v is_val.simps less_irrefl subst_Var)

  show ?thesis
    using P3 P4 by force
qed


section \<open>Type System\<close>


subsection \<open>Environments\<close>


(* Environments are represented as lists, where the head corresponds to the
   most recently inserted binding (de Bruijn-style contexts). *)
type_synonym ('a) env = "'a list"


(* insert_at xs j x inserts element x at position j in xs. *)
fun insert_at :: "'a env \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a env" where
  "insert_at xs       0       x = x # xs" |
  "insert_at []       (Suc n) x = [x]" |
  "insert_at (y # ys) (Suc n) x = y # insert_at ys n x"


(* Inserting at any position increases the environment length by exactly one. *)
lemma length_insert_at:
  "length (insert_at xs j y) = length xs + 1"
proof (induction xs arbitrary: j)
  case Nil
  then show ?case
  apply (cases j)
  apply auto
  done
next
  case (Cons a xs)
  then show ?case
  apply (cases j)
  apply simp
  by simp
qed


(* If we insert y at position j (within bounds), then the element at j is y. *)
lemma shift_eq:
  assumes "j \<le> length xs"
  shows   "(insert_at xs j y) ! j = y"
using assms
proof (induction xs arbitrary: j)
  case Nil
  then show ?case
  apply (cases j)
  apply auto
  done
next
  case (Cons y ys)
  then show ?case
  apply (cases j)
  apply auto
  done
qed


(* If we insert at position i (within bounds) and look at an index j < i,
   the prefix is unchanged. *)
lemma shift_gt:
  assumes "i \<le> length xs"
  shows "j < i \<Longrightarrow> (insert_at xs i y) ! j = xs ! j"
using assms
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  apply (cases i)
  apply simp
  by simp
next
  case (Cons a xs)
  then show ?case
  apply (cases i)
  apply auto
  using less_Suc_eq_0_disj by fastforce
qed


(* If we insert at position i and look at an index j > i,
   indices to the right are shifted by one. *)
lemma shift_lt:
  "i < j \<Longrightarrow>
  (insert_at xs i y) ! j = xs ! (j - 1)"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  apply (cases i)
  apply simp
  by simp
next
  case (Cons a xs)
  then show ?case
  apply (cases i)
  apply auto
  done
qed


(* Inserting y at the front and then U at position Suc i is the same as
   first inserting U at position i and then y at the front. *)
lemma shift_commute:
  "insert_at (insert_at xs i y1) 0 y2
   = insert_at (insert_at xs 0 y2) (Suc i) y1"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  by simp
next
  case (Cons a xs)
  then show ?case
  by simp
qed


subsection \<open>Types and Typing Rules\<close>


(* Simple types:
   - Base n : a base type identified by a natural number n.
   - Fun \<tau> U : function type from \<tau> to U (written \<tau> ⇒ U). *)
datatype type =
    Base nat
  | Fun type type    (infixr \<open>\<Rightarrow>\<close> 200)


(* Typing environments map de Bruijn indices to types by list lookup.
   The head corresponds to the most recently bound variable. *)
type_synonym tyenv = "type list"


(* Typing Rules:
     - Var : if i is in range and Γ!i = \<tau>, then variable i has type \<tau>.
     - Abs \<tau>' : if t has type \<tau>2 under Γ extended with \<tau>, then Abs \<tau>' t has type \<tau> ⇒ \<tau>2.
     - App : if s has type \<tau> ⇒ \<tau>2 and t has type \<tau>, then s · t has type \<tau>2.
     - Val : numeric literals are assigned a fixed base type (here Base 1). *)
inductive typing ::
  "tyenv \<Rightarrow> type exp \<Rightarrow> type \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  where
  Var[intro!]:
    "i < length \<Gamma> \<Longrightarrow>
     \<Gamma> ! i = \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile> Var i : \<tau>"
| Abs[intro!]:
    "\<tau>1 # \<Gamma> \<turnstile> e : \<tau>2 \<Longrightarrow>
     \<Gamma> \<turnstile> Abs \<tau>1 e : \<tau>1 \<Rightarrow> \<tau>2"
| App[intro!]:
    "\<Gamma> \<turnstile> e1 : \<tau>2 \<Rightarrow> \<tau>1 \<Longrightarrow>
     \<Gamma> \<turnstile> e2 : \<tau>2 \<Longrightarrow>
     \<Gamma> \<turnstile> e1 \<cdot> e2 : \<tau>1"
| Val[intro!]:
    "\<Gamma> \<turnstile> (Val v s) : (Base s)"


(* Elimination (inversion) rules for the typing judgment.
   They allow case analysis on a typing derivation of a specific syntactic form. *)
inductive_cases typing_elims [elim!]:
  "\<Gamma> \<turnstile> Var i : \<tau>"
  "\<Gamma> \<turnstile> e1 \<cdot> e2 : \<tau>"
  "\<Gamma> \<turnstile> Abs \<tau>1 e : \<tau>"
  "\<Gamma> \<turnstile> Val v s : \<tau>"


subsection \<open>Some examples\<close>

schematic_goal "\<Gamma> \<turnstile> Abs \<tau>1 (Var 0) : ?\<tau>"
  by force

schematic_goal "\<Gamma> \<turnstile> Abs \<tau>1 (Abs \<tau>2 (Var 1)) : ?\<tau>"
  by force

schematic_goal "\<Gamma> \<turnstile> Val v s : ?\<tau>"
  by force


schematic_goal "[] \<turnstile> (Abs ?\<tau>2 (Var 0)) \<cdot> Val v s : ?\<tau>"
 by force



schematic_goal "[] \<turnstile> Abs ?\<tau>1 (Abs ?\<tau>2 (Var 1 \<cdot> Var 0)) : ?\<tau>"
  by force


schematic_goal "\<Gamma> \<turnstile>
  Abs ?\<tau>1 (Abs ?\<tau>2 (Abs ?\<tau>3 (Var 1 \<cdot> (Var 2 \<cdot> Val 1 3 \<cdot> Var 0)))) : ?\<tau>"
  by force


schematic_goal "\<Gamma> \<turnstile>
  Abs ?\<tau>1 (Abs ?\<tau>2 (Abs ?\<tau>3 (Var 2 \<cdot> Var 0 \<cdot> (Var 1 \<cdot> Var 0)))) : ?\<tau>"
  by force


subsection \<open>Lifting preserves well-typedness\<close>


(* The lifting operation shifts free variable indices in an expression.
   This lemma shows that lifting preserves typing:
   if e is well-typed in environment \<Gamma>,
   then lifting e by i yields a well-typed term in the environment
   extended by inserting \<tau>' at position i.
   This property is crucial for the substitution lemma,
   particularly under the abstraction case. *)
lemma lift_type:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
      and "i \<le> length \<Gamma>"
  shows "insert_at \<Gamma> i \<tau>' \<turnstile> lift e i : \<tau>"
using assms
proof (induct arbitrary: i \<tau>' set: typing)
  case (Var j \<Gamma> \<tau>)
  then show ?case
  apply auto
  apply (simp add: length_insert_at)
  apply (simp add: shift_gt)
  apply (simp add: length_insert_at)
  apply (simp add: shift_lt)
  done
next
  case (Abs \<tau>2' \<tau> \<Gamma> e \<tau>2)
  then show ?case
  apply auto
  apply force
  done
next
  case (App \<Gamma> e1 \<tau>2 \<tau>1 e2)
  then show ?case
  apply auto
  done
next
  case (Val \<Gamma> s)
  then show ?case
  using typing.Val by auto
qed


subsection \<open>Substitution Lemma\<close>


(* Substitution lemma:
   If e1 is well-typed under environment \<Gamma>1,
   and e2 is well-typed under \<Gamma>2,
   and \<Gamma>1 = insert_at \<Gamma>2 i \<tau>2,
   then substituting e2 for variable i in e1 yields a well-typed term
   under \<Gamma>2 with the same type as e1.
   This formalizes that well-typedness is preserved by substitution. *)
lemma subst_lemma:
  fixes i :: nat
    and e1 e2 :: "type exp"
    and \<tau>1 \<tau>2 :: type
    and \<Gamma>1 \<Gamma>2 :: "tyenv"
  shows "\<Gamma>1 \<turnstile> e1 : \<tau>1 \<Longrightarrow>
         \<Gamma>2 \<turnstile> e2 : \<tau>2 \<Longrightarrow>
         i \<le> length \<Gamma>2 \<Longrightarrow>
         \<Gamma>1 = insert_at \<Gamma>2 i \<tau>2 \<Longrightarrow>
         \<Gamma>2 \<turnstile> e1[e2/i] : \<tau>1"
proof (induct arbitrary: \<Gamma>2 i \<tau>2 e2 set: typing)
  case (Abs \<tau>1' \<Gamma>' e' \<tau>2')
  have LIFT: "\<tau>1' # \<Gamma>2 \<turnstile> lift e2 0 : \<tau>2"
    using Abs.prems(1) lift_type by fastforce
  have LE: "Suc i \<le> length (\<tau>1' # \<Gamma>2)" using Abs.prems(2) by simp
  have ENV: "\<tau>1' # \<Gamma>' = insert_at (\<tau>1' # \<Gamma>2) (Suc i) \<tau>2"
    using Abs.prems(3) by (simp add: shift_commute)
  have IH: "\<tau>1' # \<Gamma>2 \<turnstile> e'[lift e2 0 / Suc i] : \<tau>2'"
    using Abs.hyps(2) ENV LE LIFT by blast
  show ?case
    by (simp add: IH typing.Abs)
next
  case (Var j \<Gamma> \<tau>)
  then show ?case
    apply (simp add: subst_Var)
    apply auto
    apply (simp add: shift_eq)
    apply (simp add: length_insert_at)
    apply (simp add: shift_lt)
    by (simp add: shift_gt)
next
  case (App \<Gamma> s \<tau> \<tau>' t)
  then show ?case
  by auto
next
  case (Val \<Gamma> s)
  then show ?case
  using typing.Val by fastforce
qed


subsection \<open>Subject Reduction\<close>


(* Subject reduction:
   If a term e reduces to e' by a call-by-value step,
   and e is well-typed,
   then e' is also well-typed with the same type.
   This ensures that evaluation preserves typing. *)
corollary subject_reduction:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
      and "e \<rightarrow>\<^sub>v e'"
    shows "\<Gamma> \<turnstile> e' : \<tau>"
using assms
proof (induct arbitrary: e' set: typing)
  case (Var i \<Gamma> \<tau>)
  then show ?case
  by auto
next
  case (Abs \<tau>' \<tau> \<Gamma> e \<tau>2)
  then show ?case
  by auto
next
  case (App \<Gamma> s \<tau> \<tau>2 t)
  then show ?case
  apply auto
  by (simp add: subst_lemma)
next
  case (Val \<Gamma> v)
  then show ?case
  using cbv.cases by blast
qed


(* Multi-step subject reduction:
   If e reduces to e' in zero or more steps,
   then e' has the same type as e. *)
theorem subject_reduction':
  assumes "e \<rightarrow>\<^sub>v\<^sup>* e'"
   and "\<Gamma> \<turnstile> e : \<tau>"
  shows "\<Gamma> \<turnstile> e' : \<tau>"
using assms
  by (induct set: rtranclp) (iprover intro: subject_reduction)+


subsection \<open>Progress\<close>


(* Canonical forms for function types under CBV:
   if a closed value has a function type, it must be an Abs. *)
lemma canonical_fun:
  assumes V: "is_val v"
      and T: "[] \<turnstile> v : \<tau>1 \<Rightarrow> \<tau>2"
  shows "\<exists>e. v = Abs \<tau>1 e"
using V T
proof cases
  case (v_abs t)
  then show ?thesis
  using T by blast
next
  case (v_nat n e)
  hence "[] \<turnstile> Val n e : \<tau>1 \<Rightarrow> \<tau>2" using T by simp
  then have "\<tau> \<Rightarrow> \<tau>2 = Base 1"
  apply cases
  done
  thus ?thesis by simp
qed


(* Progress: closed, well-typed terms are values or can step. *)
lemma progress:
  "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow>
   \<Gamma> = [] \<Longrightarrow>
   is_val e \<or> (\<exists>e'. e \<rightarrow>\<^sub>v e')"
proof (induction arbitrary: \<tau> set: typing)
  case (Var i \<Gamma>' \<tau>)
  then show ?case
  by simp
next
  case (Abs \<tau>1 \<Gamma> t \<tau>2)
  then show ?case
  by auto
next
  case (Val \<Gamma>' s)
  then show ?case
  by auto
next
  case (App \<Gamma>' t1 \<tau>2 \<tau>1 t2)
  have H1: "\<Gamma>' \<turnstile> t1 : \<tau>2 \<Rightarrow> \<tau>1"
    by (simp add: App.hyps(1))
  have H2: "\<Gamma>' = []"
    by (simp add: App.prems)
  have P1: "is_val t1 \<or> (\<exists>t1'. t1 \<rightarrow>\<^sub>v t1')"
    by (simp add: App.IH(1) H2)
  have P2: "is_val t1 \<Longrightarrow>
	    (\<exists>t'. (t1 \<cdot> t2) \<rightarrow>\<^sub>v t')"
    using App.IH(2) H1 H2 canonical_fun by blast
  show ?case
    using P1 P2 by blast
qed


(* Progress: a simpler corollary. *)
corollary progress':
  assumes "[] \<turnstile> e : \<tau>"
  shows "is_val e \<or> (\<exists>e'. e \<rightarrow>\<^sub>v e')"
using assms progress by auto


subsection \<open>Soundness\<close>


(* Type soundness theorem:
   If a closed term is well-typed and reduces (in zero or more steps)
   to some term e', then e' is either a value or can take a further step.
   This combines subject reduction and progress to establish
   the standard type soundness property of the language. *)
theorem type_soundness:
  assumes WT: "[] \<turnstile> e : \<tau>"
      and STEPS: "e \<rightarrow>\<^sub>v\<^sup>* e'"
  shows "is_val e' \<or> (\<exists>u. e' \<rightarrow>\<^sub>v u)"
proof -
  have "[] \<turnstile> e' : \<tau>" using STEPS WT subject_reduction' by blast
  thus ?thesis using progress' by blast
qed


subsection \<open>Closed\<close>


(* Set of free variables *)
primrec fv :: "type exp => nat set" where
    fv_Var: "fv (Var i) = {i}"
  | fv_App: "fv (t \<cdot> u) = fv t \<union> fv u"
  | fv_Abs: "fv (Abs \<tau>' t) = (\<lambda> i. i - 1) ` (fv t - {0})"
  | fv_Val: "fv (Val t s) = {}"


(* Testing free variables *)
value "fv (Abs \<tau>' (Abs \<tau>' (Abs \<tau>' (Var 5 \<cdot> (Var 2 \<cdot> Val 1 8 \<cdot> Var 0)))))"
value "fv (Abs \<tau>' (Abs \<tau>' (Abs \<tau>' (Var 2 \<cdot> Var 0 \<cdot> (Var 1 \<cdot> Var 0)))))"


abbreviation is_closed :: "type exp \<Rightarrow> bool" where
  "is_closed t \<equiv> fv t = {}"


(* The length of the typing environment conrresponds the indices of free variables. *)
lemma envlen_fv:
  assumes Ty: "\<Gamma> \<turnstile> t : \<tau>"
  shows "\<forall> i \<in> fv t. i < length \<Gamma>"
using assms
proof (induction arbitrary: \<tau> set: typing)
  case (Var i \<Gamma>' \<tau>)
  then show ?case
  apply auto
  done
next
  case (Abs \<tau>1 \<Gamma> t \<tau>2)
  then show ?case
  apply auto
  done
next
  case (App \<Gamma> s \<tau> \<tau>2 t)
  then show ?case
  apply auto
  done
next
  case (Val \<Gamma> s)
  then show ?case
  apply auto
  done
qed


(* If typable, then it is closed. *)
lemma emp_env_closed:
  assumes "[] \<turnstile> t : \<tau>"
    shows "fv t = {}"
using assms envlen_fv by fastforce


end
