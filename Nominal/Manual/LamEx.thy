theory LamEx
imports "../Nominal2_Atoms" "../Nominal2_Eqvt" "../Nominal2_Supp" "../Abs"
begin

atom_decl name

datatype rlam =
  rVar "name"
| rApp "rlam" "rlam"
| rLam "name" "rlam"

fun
  rfv :: "rlam \<Rightarrow> atom set"
where
  rfv_var: "rfv (rVar a) = {atom a}"
| rfv_app: "rfv (rApp t1 t2) = (rfv t1) \<union> (rfv t2)"
| rfv_lam: "rfv (rLam a t) = (rfv t) - {atom a}"

instantiation rlam :: pt
begin

primrec
  permute_rlam
where
  "permute_rlam pi (rVar a) = rVar (pi \<bullet> a)"
| "permute_rlam pi (rApp t1 t2) = rApp (permute_rlam pi t1) (permute_rlam pi t2)"
| "permute_rlam pi (rLam a t) = rLam (pi \<bullet> a) (permute_rlam pi t)"

instance
apply default
apply(induct_tac [!] x)
apply(simp_all)
done

end

instantiation rlam :: fs
begin

lemma neg_conj:
  "\<not>(P \<and> Q) \<longleftrightarrow> (\<not>P) \<or> (\<not>Q)"
  by simp

instance
apply default
apply(induct_tac x)
(* var case *)
apply(simp add: supp_def)
apply(fold supp_def)[1]
apply(simp add: supp_at_base)
(* app case *)
apply(simp only: supp_def)
apply(simp only: permute_rlam.simps) 
apply(simp only: rlam.inject) 
apply(simp only: neg_conj)
apply(simp only: Collect_disj_eq)
apply(simp only: infinite_Un)
apply(simp only: Collect_disj_eq)
apply(simp)
(* lam case *)
apply(simp only: supp_def)
apply(simp only: permute_rlam.simps) 
apply(simp only: rlam.inject) 
apply(simp only: neg_conj)
apply(simp only: Collect_disj_eq)
apply(simp only: infinite_Un)
apply(simp only: Collect_disj_eq)
apply(simp)
apply(fold supp_def)[1]
apply(simp add: supp_at_base)
done

end


(* for the eqvt proof of the alpha-equivalence *)
declare permute_rlam.simps[eqvt]

lemma rfv_eqvt[eqvt]:
  shows "(pi\<bullet>rfv t) = rfv (pi\<bullet>t)"
apply(induct t)
apply(simp_all)
apply(simp add: permute_set_eq atom_eqvt)
apply(simp add: union_eqvt)
apply(simp add: Diff_eqvt)
apply(simp add: permute_set_eq atom_eqvt)
done

inductive
    alpha :: "rlam \<Rightarrow> rlam \<Rightarrow> bool" ("_ \<approx>a _" [100, 100] 100)
where
  a1: "a = b \<Longrightarrow> (rVar a) \<approx>a (rVar b)"
| a2: "\<lbrakk>t1 \<approx>a t2; s1 \<approx>a s2\<rbrakk> \<Longrightarrow> rApp t1 s1 \<approx>a rApp t2 s2"
| a3: "\<exists>pi. (rfv t - {atom a} = rfv s - {atom b} \<and> (rfv t - {atom a})\<sharp>* pi \<and> (pi \<bullet> t) \<approx>a s)
       \<Longrightarrow> rLam a t \<approx>a rLam b s"

lemma a3_inverse:
  assumes "rLam a t \<approx>a rLam b s"
  shows "\<exists>pi. (rfv t - {atom a} = rfv s - {atom b} \<and> (rfv t - {atom a})\<sharp>* pi \<and> (pi \<bullet> t) \<approx>a s)"
using assms
apply(erule_tac alpha.cases)
apply(auto)
done

text {* should be automatic with new version of eqvt-machinery *}
lemma alpha_eqvt:
  shows "t \<approx>a s \<Longrightarrow> (pi \<bullet> t) \<approx>a (pi \<bullet> s)"
apply(induct rule: alpha.induct)
apply(simp add: a1)
apply(simp add: a2)
apply(simp)
apply(rule a3)
apply(erule conjE)
apply(erule exE)
apply(erule conjE)
apply(rule_tac x="pi \<bullet> pia" in exI)
apply(rule conjI)
apply(rule_tac ?p1="- pi" in permute_eq_iff[THEN iffD1])
apply(simp only: Diff_eqvt rfv_eqvt insert_eqvt atom_eqvt empty_eqvt)
apply(simp)
apply(rule conjI)
apply(rule_tac ?p1="- pi" in fresh_star_permute_iff[THEN iffD1])
apply(simp add: Diff_eqvt rfv_eqvt atom_eqvt insert_eqvt empty_eqvt)
apply(subst permute_eqvt[symmetric])
apply(simp)
done

lemma alpha_refl:
  shows "t \<approx>a t"
apply(induct t rule: rlam.induct)
apply(simp add: a1)
apply(simp add: a2)
apply(rule a3)
apply(rule_tac x="0" in exI)
apply(simp_all add: fresh_star_def fresh_zero_perm)
done

lemma alpha_sym:
  shows "t \<approx>a s \<Longrightarrow> s \<approx>a t"
apply(induct rule: alpha.induct)
apply(simp add: a1)
apply(simp add: a2)
apply(rule a3)
apply(erule exE)
apply(rule_tac x="- pi" in exI)
apply(simp)
apply(simp add: fresh_star_def fresh_minus_perm)
apply(erule conjE)+
apply(rotate_tac 3)
apply(drule_tac pi="- pi" in alpha_eqvt)
apply(simp)
done

lemma alpha_trans:
  shows "t1 \<approx>a t2 \<Longrightarrow> t2 \<approx>a t3 \<Longrightarrow> t1 \<approx>a t3"
apply(induct arbitrary: t3 rule: alpha.induct)
apply(erule alpha.cases)
apply(simp_all)
apply(simp add: a1)
apply(rotate_tac 4)
apply(erule alpha.cases)
apply(simp_all)
apply(simp add: a2)
apply(rotate_tac 1)
apply(erule alpha.cases)
apply(simp_all)
apply(erule conjE)+
apply(erule exE)+
apply(erule conjE)+
apply(rule a3)
apply(rule_tac x="pia + pi" in exI)
apply(simp add: fresh_star_plus)
apply(drule_tac x="- pia \<bullet> sa" in spec)
apply(drule mp)
apply(rotate_tac 7)
apply(drule_tac pi="- pia" in alpha_eqvt)
apply(simp)
apply(rotate_tac 9)
apply(drule_tac pi="pia" in alpha_eqvt)
apply(simp)
done

lemma alpha_equivp:
  shows "equivp alpha"
  apply(rule equivpI)
  unfolding reflp_def symp_def transp_def
  apply(auto intro: alpha_refl alpha_sym alpha_trans)
  done

lemma alpha_rfv:
  shows "t \<approx>a s \<Longrightarrow> rfv t = rfv s"
  apply(induct rule: alpha.induct)
  apply(simp_all)
  done

inductive
    alpha2 :: "rlam \<Rightarrow> rlam \<Rightarrow> bool" ("_ \<approx>a2 _" [100, 100] 100)
where
  a21: "a = b \<Longrightarrow> (rVar a) \<approx>a2 (rVar b)"
| a22: "\<lbrakk>t1 \<approx>a2 t2; s1 \<approx>a2 s2\<rbrakk> \<Longrightarrow> rApp t1 s1 \<approx>a2 rApp t2 s2"
| a23: "(a = b \<and> t \<approx>a2 s) \<or> (a \<noteq> b \<and> ((a \<leftrightarrow> b) \<bullet> t) \<approx>a2 s \<and> atom b \<notin> rfv t)\<Longrightarrow> rLam a t \<approx>a2 rLam b s"

lemma fv_vars:
  fixes a::name
  assumes a1: "\<forall>x \<in> rfv t - {atom a}. pi \<bullet> x = x"
  shows "(pi \<bullet> t) \<approx>a2 ((a \<leftrightarrow> (pi \<bullet> a)) \<bullet> t)"
using a1
apply(induct t)
apply(auto)
apply(rule a21)
apply(case_tac "name = a")
apply(simp)
apply(simp)
defer
apply(rule a22)
apply(simp)
apply(simp)
apply(rule a23)
apply(case_tac "a = name")
apply(simp)
oops


lemma 
  assumes a1: "t \<approx>a2 s"
  shows "t \<approx>a s"
using a1
apply(induct)
apply(rule alpha.intros)
apply(simp)
apply(rule alpha.intros)
apply(simp)
apply(simp)
apply(rule alpha.intros)
apply(erule disjE)
apply(rule_tac x="0" in exI)
apply(simp add: fresh_star_def fresh_zero_perm)
apply(erule conjE)+
apply(drule alpha_rfv)
apply(simp)
apply(rule_tac x="(a \<leftrightarrow> b)" in exI)
apply(simp)
apply(erule conjE)+
apply(rule conjI)
apply(drule alpha_rfv)
apply(drule sym)
apply(simp)
apply(simp add: rfv_eqvt[symmetric])
defer
apply(subgoal_tac "atom a \<sharp> (rfv t - {atom a})")
apply(subgoal_tac "atom b \<sharp> (rfv t - {atom a})")

defer
sorry

lemma 
  assumes a1: "t \<approx>a s"
  shows "t \<approx>a2 s"
using a1
apply(induct)
apply(rule alpha2.intros)
apply(simp)
apply(rule alpha2.intros)
apply(simp)
apply(simp)
apply(clarify)
apply(rule alpha2.intros)
apply(frule alpha_rfv)
apply(rotate_tac 4)
apply(drule sym)
apply(simp)
apply(drule sym)
apply(simp)
oops

quotient_type lam = rlam / alpha
  by (rule alpha_equivp)

quotient_definition
  "Var :: name \<Rightarrow> lam"
is
  "rVar"

quotient_definition
   "App :: lam \<Rightarrow> lam \<Rightarrow> lam"
is
  "rApp"

quotient_definition
  "Lam :: name \<Rightarrow> lam \<Rightarrow> lam"
is
  "rLam"

quotient_definition
  "fv :: lam \<Rightarrow> atom set"
is
  "rfv"

lemma perm_rsp[quot_respect]:
  "(op = ===> alpha ===> alpha) permute permute"
  apply(auto)
  apply(rule alpha_eqvt)
  apply(simp)
  done

lemma rVar_rsp[quot_respect]:
  "(op = ===> alpha) rVar rVar"
  by (auto intro: a1)

lemma rApp_rsp[quot_respect]: 
  "(alpha ===> alpha ===> alpha) rApp rApp"
  by (auto intro: a2)

lemma rLam_rsp[quot_respect]: 
  "(op = ===> alpha ===> alpha) rLam rLam"
  apply(auto)
  apply(rule a3)
  apply(rule_tac x="0" in exI)
  unfolding fresh_star_def 
  apply(simp add: fresh_star_def fresh_zero_perm)
  apply(simp add: alpha_rfv)
  done

lemma rfv_rsp[quot_respect]: 
  "(alpha ===> op =) rfv rfv"
apply(simp add: alpha_rfv)
done


section {* lifted theorems *}

lemma lam_induct:
  "\<lbrakk>\<And>name. P (Var name);
    \<And>lam1 lam2. \<lbrakk>P lam1; P lam2\<rbrakk> \<Longrightarrow> P (App lam1 lam2);
    \<And>name lam. P lam \<Longrightarrow> P (Lam name lam)\<rbrakk> 
    \<Longrightarrow> P lam"
  apply (lifting rlam.induct)
  done

instantiation lam :: pt
begin

quotient_definition
  "permute_lam :: perm \<Rightarrow> lam \<Rightarrow> lam"
is
  "permute :: perm \<Rightarrow> rlam \<Rightarrow> rlam"

lemma permute_lam [simp]:
  shows "pi \<bullet> Var a = Var (pi \<bullet> a)"
  and   "pi \<bullet> App t1 t2 = App (pi \<bullet> t1) (pi \<bullet> t2)"
  and   "pi \<bullet> Lam a t = Lam (pi \<bullet> a) (pi \<bullet> t)"
apply(lifting permute_rlam.simps)
done

instance
apply default
apply(induct_tac [!] x rule: lam_induct)
apply(simp_all)
done

end

lemma fv_lam [simp]: 
  shows "fv (Var a) = {atom a}"
  and   "fv (App t1 t2) = fv t1 \<union> fv t2"
  and   "fv (Lam a t) = fv t - {atom a}"
apply(lifting rfv_var rfv_app rfv_lam)
done

lemma fv_eqvt:
  shows "(p \<bullet> fv t) = fv (p \<bullet> t)"
apply(lifting rfv_eqvt)
done

lemma a1: 
  "a = b \<Longrightarrow> Var a = Var b"
  by  (lifting a1)

lemma a2: 
  "\<lbrakk>x = xa; xb = xc\<rbrakk> \<Longrightarrow> App x xb = App xa xc"
  by  (lifting a2)

lemma a3: 
  "\<lbrakk>\<exists>pi. (fv t - {atom a} = fv s - {atom b} \<and> (fv t - {atom a})\<sharp>* pi \<and> (pi \<bullet> t) = s)\<rbrakk> 
   \<Longrightarrow> Lam a t = Lam b s"
  apply  (lifting a3)
  done

lemma a3_inv:
  assumes "Lam a t = Lam b s"
  shows "\<exists>pi. (fv t - {atom a} = fv s - {atom b} \<and> (fv t - {atom a})\<sharp>* pi \<and> (pi \<bullet> t) = s)"
using assms
apply(lifting a3_inverse)
done

lemma alpha_cases: 
  "\<lbrakk>a1 = a2; \<And>a b. \<lbrakk>a1 = Var a; a2 = Var b; a = b\<rbrakk> \<Longrightarrow> P;
    \<And>x xa xb xc. \<lbrakk>a1 = App x xb; a2 = App xa xc; x = xa; xb = xc\<rbrakk> \<Longrightarrow> P;
    \<And>t a s b. \<lbrakk>a1 = Lam a t; a2 = Lam b s; 
         \<exists>pi. fv t - {atom a} = fv s - {atom b} \<and> (fv t - {atom a}) \<sharp>* pi \<and> (pi \<bullet> t) = s\<rbrakk> 
   \<Longrightarrow> P\<rbrakk>
    \<Longrightarrow> P"
  by (lifting alpha.cases)

(* not sure whether needed *)
lemma alpha_induct: 
  "\<lbrakk>qx = qxa; \<And>a b. a = b \<Longrightarrow> qxb (Var a) (Var b);
    \<And>x xa xb xc. \<lbrakk>x = xa; qxb x xa; xb = xc; qxb xb xc\<rbrakk> \<Longrightarrow> qxb (App x xb) (App xa xc);
     \<And>t a s b.
        \<lbrakk>\<exists>pi. fv t - {atom a} = fv s - {atom b} \<and>
         (fv t - {atom a}) \<sharp>* pi \<and> ((pi \<bullet> t) = s \<and> qxb (pi \<bullet> t) s)\<rbrakk> 
     \<Longrightarrow> qxb (Lam a t) (Lam b s)\<rbrakk>
    \<Longrightarrow> qxb qx qxa"
  by (lifting alpha.induct)

(* should they lift automatically *)
lemma lam_inject [simp]: 
  shows "(Var a = Var b) = (a = b)"
  and   "(App t1 t2 = App s1 s2) = (t1 = s1 \<and> t2 = s2)"
apply(lifting rlam.inject(1) rlam.inject(2))
apply(regularize)
prefer 2
apply(regularize)
prefer 2
apply(auto)
apply(drule alpha.cases)
apply(simp_all)
apply(simp add: alpha.a1)
apply(drule alpha.cases)
apply(simp_all)
apply(drule alpha.cases)
apply(simp_all)
apply(rule alpha.a2)
apply(simp_all)
done

lemma Lam_pseudo_inject:
  shows "(Lam a t = Lam b s) = 
      (\<exists>pi. (fv t - {atom a} = fv s - {atom b} \<and> (fv t - {atom a})\<sharp>* pi \<and> (pi \<bullet> t) = s))"
apply(rule iffI)
apply(rule a3_inv)
apply(assumption)
apply(rule a3)
apply(assumption)
done

lemma rlam_distinct:
  shows "\<not>(rVar nam \<approx>a rApp rlam1' rlam2')"
  and   "\<not>(rApp rlam1' rlam2' \<approx>a rVar nam)"
  and   "\<not>(rVar nam \<approx>a rLam nam' rlam')"
  and   "\<not>(rLam nam' rlam' \<approx>a rVar nam)"
  and   "\<not>(rApp rlam1 rlam2 \<approx>a rLam nam' rlam')"
  and   "\<not>(rLam nam' rlam' \<approx>a rApp rlam1 rlam2)"
apply auto
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
apply (erule alpha.cases)
apply (simp_all only: rlam.distinct)
done

lemma lam_distinct[simp]:
  shows "Var nam \<noteq> App lam1' lam2'"
  and   "App lam1' lam2' \<noteq> Var nam"
  and   "Var nam \<noteq> Lam nam' lam'"
  and   "Lam nam' lam' \<noteq> Var nam"
  and   "App lam1 lam2 \<noteq> Lam nam' lam'"
  and   "Lam nam' lam' \<noteq> App lam1 lam2"
apply(lifting rlam_distinct(1) rlam_distinct(2) rlam_distinct(3) rlam_distinct(4) rlam_distinct(5) rlam_distinct(6))
done

lemma var_supp1:
  shows "(supp (Var a)) = (supp a)"
  apply (simp add: supp_def)
  done

lemma var_supp:
  shows "(supp (Var a)) = {a:::name}"
  using var_supp1 by (simp add: supp_at_base)

lemma app_supp:
  shows "supp (App t1 t2) = (supp t1) \<union> (supp t2)"
apply(simp only: supp_def lam_inject)
apply(simp add: Collect_imp_eq Collect_neg_eq)
done

(* supp for lam *)
lemma lam_supp1:
  shows "(supp (atom x, t)) supports (Lam x t) "
apply(simp add: supports_def)
apply(fold fresh_def)
apply(simp add: fresh_Pair swap_fresh_fresh)
apply(clarify)
apply(subst swap_at_base_simps(3))
apply(simp_all add: fresh_atom)
done

lemma lam_fsupp1:
  assumes a: "finite (supp t)"
  shows "finite (supp (Lam x t))"
apply(rule supports_finite)
apply(rule lam_supp1)
apply(simp add: a supp_Pair supp_atom)
done

instance lam :: fs
apply(default)
apply(induct_tac x rule: lam_induct)
apply(simp add: var_supp)
apply(simp add: app_supp)
apply(simp add: lam_fsupp1)
done

lemma supp_fv:
  shows "supp t = fv t"
apply(induct t rule: lam_induct)
apply(simp add: var_supp)
apply(simp add: app_supp)
apply(subgoal_tac "supp (Lam name lam) = supp (Abs {atom name} lam)")
apply(simp add: supp_Abs)
apply(simp (no_asm) add: supp_def permute_set_eq atom_eqvt)
apply(simp add: Lam_pseudo_inject)
apply(simp add: Abs_eq_iff alpha_gen)
apply(simp add: supp_eqvt[symmetric] fv_eqvt[symmetric])
done

lemma lam_supp2:
  shows "supp (Lam x t) = supp (Abs {atom x} t)"
apply(simp add: supp_def permute_set_eq atom_eqvt)
apply(simp add: Lam_pseudo_inject)
apply(simp add: Abs_eq_iff supp_fv alpha_gen)
done

lemma lam_supp:
  shows "supp (Lam x t) = ((supp t) - {atom x})"
apply(simp add: lam_supp2)
apply(simp add: supp_Abs)
done

lemma fresh_lam:
  "(atom a \<sharp> Lam b t) \<longleftrightarrow> (a = b) \<or> (a \<noteq> b \<and> atom a \<sharp> t)"
apply(simp add: fresh_def)
apply(simp add: lam_supp)
apply(auto)
done

lemma lam_induct_strong:
  fixes a::"'a::fs"
  assumes a1: "\<And>name b. P b (Var name)"
  and     a2: "\<And>lam1 lam2 b. \<lbrakk>\<And>c. P c lam1; \<And>c. P c lam2\<rbrakk> \<Longrightarrow> P b (App lam1 lam2)"
  and     a3: "\<And>name lam b. \<lbrakk>\<And>c. P c lam; (atom name) \<sharp> b\<rbrakk> \<Longrightarrow> P b (Lam name lam)"
  shows "P a lam"
proof -
  have "\<And>pi a. P a (pi \<bullet> lam)" 
  proof (induct lam rule: lam_induct)
    case (1 name pi)
    show "P a (pi \<bullet> Var name)"
      apply (simp)
      apply (rule a1)
      done
  next
    case (2 lam1 lam2 pi)
    have b1: "\<And>pi a. P a (pi \<bullet> lam1)" by fact
    have b2: "\<And>pi a. P a (pi \<bullet> lam2)" by fact
    show "P a (pi \<bullet> App lam1 lam2)"
      apply (simp)
      apply (rule a2)
      apply (rule b1)
      apply (rule b2)
      done
  next
    case (3 name lam pi a)
    have b: "\<And>pi a. P a (pi \<bullet> lam)" by fact
    obtain c::name where fr: "atom c\<sharp>(a, pi\<bullet>name, pi\<bullet>lam)"
      apply(rule obtain_atom)
      apply(auto)
      sorry
    from b fr have p: "P a (Lam c (((c \<leftrightarrow> (pi \<bullet> name)) + pi)\<bullet>lam))" 
      apply -
      apply(rule a3)
      apply(blast)
      apply(simp add: fresh_Pair)
      done
    have eq: "(atom c \<rightleftharpoons> atom (pi\<bullet>name)) \<bullet> Lam (pi \<bullet> name) (pi \<bullet> lam) = Lam (pi \<bullet> name) (pi \<bullet> lam)"
      apply(rule swap_fresh_fresh)
      using fr
      apply(simp add: fresh_lam fresh_Pair)
      apply(simp add: fresh_lam fresh_Pair)
      done
    show "P a (pi \<bullet> Lam name lam)" 
      apply (simp)
      apply(subst eq[symmetric])
      using p
      apply(simp only: permute_lam)
      apply(simp add: flip_def)
      done
  qed
  then have "P a (0 \<bullet> lam)" by blast
  then show "P a lam" by simp 
qed


lemma var_fresh:
  fixes a::"name"
  shows "(atom a \<sharp> (Var b)) = (atom a \<sharp> b)"
  apply(simp add: fresh_def)
  apply(simp add: var_supp1)
  done



end

