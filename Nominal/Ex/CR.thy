(* CR_Takahashi from Nominal1 ported to Nominal2 *)
theory CR 
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_function
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Lam [x]. t)[y ::= s] = Lam [x].(t[y ::= s])"
  unfolding eqvt_def subst_graph_def
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  apply(auto)
  apply(rule_tac y="a" and c="(aa, b)" in lam.strong_exhaust)
  apply(blast)+
  apply(simp_all add: fresh_star_def fresh_Pair_elim)
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp_all add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  done

nominal_termination (eqvt)
  by lexicographic_order

lemma forget:
  shows "atom x \<sharp> t \<Longrightarrow> t[x ::= s] = t"
  by (nominal_induct t avoiding: x s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma fresh_fact:
  fixes z::"name"
  assumes a: "atom z \<sharp> s"
      and b: "z = y \<or> atom z \<sharp> t"
  shows "atom z \<sharp> t[y ::= s]"
  using a b
  by (nominal_induct t avoiding: z y s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma substitution_lemma:
  assumes a: "x \<noteq> y" "atom x \<sharp> u"
  shows "t[x ::= s][y ::= u] = t[y ::= u][x ::= s[y ::= u]]"
  using a
  by (nominal_induct t avoiding: x y s u rule: lam.strong_induct)
     (auto simp add: fresh_fact forget)

lemma subst_rename:
  assumes a: "atom y \<sharp> t"
  shows "t[x ::= s] = ((y \<leftrightarrow> x) \<bullet>t)[y ::= s]"
  using a
  by (nominal_induct t avoiding: x y s rule: lam.strong_induct)
     (auto simp add: lam.fresh fresh_at_base)

lemma supp_subst:
  shows "supp (t[x ::= s]) \<subseteq> (supp t - {atom x}) \<union> supp s"
  by (induct t x s rule: subst.induct) (auto simp add: lam.supp supp_at_base)

inductive
  beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>b _" [80,80] 80)
where
  b1[intro]: "t1 \<longrightarrow>b t2 \<Longrightarrow> App t1 s \<longrightarrow>b App t2 s"
| b2[intro]: "s1 \<longrightarrow>b s2 \<Longrightarrow> App t s1 \<longrightarrow>b App t s2"
| b3[intro]: "t1 \<longrightarrow>b t2 \<Longrightarrow> Lam [x]. t1 \<longrightarrow>b Lam [x]. t2"
| b4[intro]: "atom x \<sharp> s \<Longrightarrow> App (Lam [x]. t) s \<longrightarrow>b t[x ::= s]"

equivariance beta

nominal_inductive beta
  avoids b3: x
       | b4: x
  by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

section {* Transitive Closure of Beta *}

inductive
  beta_star :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>b* _" [80,80] 80)
where
  bs1[intro, simp]: "M \<longrightarrow>b* M"
| bs2[intro]: "\<lbrakk>M1\<longrightarrow>b* M2; M2 \<longrightarrow>b M3\<rbrakk> \<Longrightarrow> M1 \<longrightarrow>b* M3"

equivariance beta_star

lemma bs3[intro, trans]:
  assumes "A \<longrightarrow>b* B"
  and     "B \<longrightarrow>b* C"
  shows   "A \<longrightarrow>b* C"
  using assms(2) assms(1)
  by induct auto

section {* One-Reduction *}

inductive
  One :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>1 _" [80,80] 80)
where
  o1[intro]: "Var x \<longrightarrow>1 Var x"
| o2[intro]: "\<lbrakk>t1 \<longrightarrow>1 t2; s1 \<longrightarrow>1 s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>1 App t2 s2"
| o3[intro]: "t1 \<longrightarrow>1 t2 \<Longrightarrow> Lam [x].t1 \<longrightarrow>1 Lam [x].t2"
| o4[intro]: "\<lbrakk>atom x \<sharp> (s1, s2); t1 \<longrightarrow>1 t2; s1 \<longrightarrow>1 s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>1 t2[x ::= s2]"

equivariance One

nominal_inductive One
  avoids o3: "x"
      |  o4: "x"
  by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

lemma One_refl:
  shows "t \<longrightarrow>1 t"
  by (nominal_induct t rule: lam.strong_induct) (auto)

lemma One_subst:
  assumes a: "t1 \<longrightarrow>1 t2" "s1 \<longrightarrow>1 s2"
  shows "t1[x ::= s1] \<longrightarrow>1 t2[x ::= s2]"
  using a
  by (nominal_induct t1 t2 avoiding: s1 s2 x rule: One.strong_induct)
     (auto simp add: substitution_lemma fresh_at_base fresh_fact fresh_Pair)

lemma better_o4_intro:
  assumes a: "t1 \<longrightarrow>1 t2" "s1 \<longrightarrow>1 s2"
  shows "App (Lam [x]. t1) s1 \<longrightarrow>1 t2[ x ::= s2]"
proof -
  obtain y::"name" where fs: "atom y \<sharp> (x, t1, s1, t2, s2)" by (rule obtain_fresh)
  have "App (Lam [x]. t1) s1 = App (Lam [y]. ((y \<leftrightarrow> x) \<bullet> t1)) s1" using fs
    by (auto simp add: lam.eq_iff Abs1_eq_iff' flip_def fresh_Pair fresh_at_base)
  also have "\<dots> \<longrightarrow>1 ((y \<leftrightarrow> x) \<bullet> t2)[y ::= s2]" using fs a by (auto simp add: One.eqvt)
  also have "\<dots> = t2[x ::= s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>1 t2[x ::= s2]" by simp
qed

lemma One_Var:
  assumes a: "Var x \<longrightarrow>1 M"
  shows "M = Var x"
  using a by (cases rule: One.cases) (simp_all)

lemma One_Lam:
  assumes a: "Lam [x].t \<longrightarrow>1 s" "atom x \<sharp> s"
  shows "\<exists>t'. s = Lam [x].t' \<and> t \<longrightarrow>1 t'"
  using a
  apply (cases rule: One.cases)
  apply (auto simp add: Abs1_eq_iff)
  apply (rule_tac x="(atom xa \<rightleftharpoons> atom x) \<bullet> t2" in exI)
  apply (auto simp add: fresh_permute_left lam.fresh)
  by (metis swap_commute One.eqvt)

lemma One_App:
  assumes a: "App t s \<longrightarrow>1 r"
  shows "(\<exists>t' s'. r = App t' s' \<and> t \<longrightarrow>1 t' \<and> s \<longrightarrow>1 s') \<or>
         (\<exists>x p p' s'. r = p'[x ::= s'] \<and> t = Lam [x].p \<and> p \<longrightarrow>1 p' \<and> s \<longrightarrow>1 s' \<and> atom x \<sharp> (s,s'))"
  using a by (cases rule: One.cases) auto

lemma One_preserves_fresh:
  fixes x::"name"
  assumes a: "M \<longrightarrow>1 N"
  shows "atom x \<sharp> M \<Longrightarrow> atom x \<sharp> N"
  using a
  by (induct, auto simp add: lam.fresh)
     (metis fresh_fact)+

(* TODO *)
lemma One_strong_cases[consumes 1]:
  "\<lbrakk> a1 \<longrightarrow>1 a2; \<And>x. \<lbrakk>a1 = Var x; a2 = Var x\<rbrakk> \<Longrightarrow> P;
 \<And>t1 t2 s1 s2. \<lbrakk>a1 = App t1 s1; a2 = App t2 s2;  t1 \<longrightarrow>1 t2;  s1 \<longrightarrow>1 s2\<rbrakk> \<Longrightarrow> P;
 \<And>t1 t2. (\<lbrakk>atom xa \<sharp> a1; atom xa \<sharp> a2\<rbrakk> \<Longrightarrow> a1 = Lam [xa].t1 \<and> a2 = Lam [xa].t2 \<and>  t1 \<longrightarrow>1 t2) \<Longrightarrow> P;
 \<And>s1 s2 t1 t2.
    (\<lbrakk>atom xaa \<sharp> a1; atom xaa \<sharp> a2\<rbrakk>
     \<Longrightarrow> a1 = App (Lam [xaa].t1) s1 \<and> a2 = t2[xaa::=s2] \<and> atom xaa \<sharp> (s1, s2) \<and>  t1 \<longrightarrow>1 t2 \<and>  s1 \<longrightarrow>1 s2) \<Longrightarrow>
    P\<rbrakk>
  \<Longrightarrow> P"
  apply (nominal_induct avoiding: a1 a2 rule: One.strong_induct)
  apply blast
  apply blast
  apply (simp add: fresh_Pair_elim Abs1_eq_iff lam.fresh)
  apply (case_tac "xa = x")
  apply (simp_all)[2]
  apply blast
  apply (rotate_tac 6)
  apply (drule_tac x="(atom x \<rightleftharpoons> atom xa) \<bullet> t1" in meta_spec)
  apply (rotate_tac -1)
  apply (drule_tac x="(atom x \<rightleftharpoons> atom xa) \<bullet> t2" in meta_spec)
  apply (simp add: One.eqvt fresh_permute_left)
  apply (simp add: fresh_Pair_elim Abs1_eq_iff lam.fresh)
  apply (case_tac "xaa = x")
  apply (simp_all add: fresh_Pair)[2]
  apply blast
  apply (rotate_tac -2)
  apply (drule_tac x="s1" in meta_spec)
  apply (rotate_tac -1)
  apply (drule_tac x="s2" in meta_spec)
  apply (rotate_tac -1)
  apply (drule_tac x="(atom x \<rightleftharpoons> atom xaa) \<bullet> t1" in meta_spec)
  apply (rotate_tac -1)
  apply (drule_tac x="(atom x \<rightleftharpoons> atom xaa) \<bullet> t2" in meta_spec)
  apply (rotate_tac -1)
  apply (simp add: One_preserves_fresh fresh_permute_left One.eqvt)
  by (metis Nominal2_Base.swap_commute One_preserves_fresh flip_def subst_rename)

lemma One_Redex:
  assumes a: "App (Lam [x].t) s \<longrightarrow>1 r" "atom x \<sharp> (s,r)"
  shows "(\<exists>t' s'. r = App (Lam [x].t') s' \<and> t \<longrightarrow>1 t' \<and> s \<longrightarrow>1 s') \<or>
         (\<exists>t' s'. r = t'[x ::= s'] \<and> t \<longrightarrow>1 t' \<and> s \<longrightarrow>1 s')"
  using a
  by (cases rule: One_strong_cases)
     (auto dest!: One_Lam simp add: fresh_Pair lam.fresh Abs1_eq_iff)

inductive
  One_star :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>1* _" [80,80] 80)
where
  os1[intro, simp]: "t \<longrightarrow>1* t"
| os2[intro]: "t \<longrightarrow>1* r \<Longrightarrow> r \<longrightarrow>1 s \<Longrightarrow> t \<longrightarrow>1* s"

lemma os3[intro, trans]:
  assumes a1: "M1 \<longrightarrow>1* M2"
  and     a2: "M2 \<longrightarrow>1* M3"
  shows "M1 \<longrightarrow>1* M3"
  using a2 a1
  by induct auto

section {* Complete Development Reduction *}

inductive
  Dev :: "lam \<Rightarrow> lam \<Rightarrow> bool" (" _ \<longrightarrow>d _" [80,80] 80)
where
  d1[intro]: "Var x \<longrightarrow>d Var x"
| d2[intro]: "t \<longrightarrow>d s \<Longrightarrow> Lam [x].t \<longrightarrow>d Lam[x].s"
| d3[intro]: "\<lbrakk>\<not>(\<exists>y t'. t1 = Lam [y].t'); t1 \<longrightarrow>d t2; s1 \<longrightarrow>d s2\<rbrakk> \<Longrightarrow> App t1 s1 \<longrightarrow>d App t2 s2"
| d4[intro]: "\<lbrakk>atom x \<sharp> (s1,s2); t1 \<longrightarrow>d t2; s1 \<longrightarrow>d s2\<rbrakk> \<Longrightarrow> App (Lam [x].t1) s1 \<longrightarrow>d t2[x::=s2]"

equivariance Dev
nominal_inductive Dev
  avoids d2: "x"
      |  d4: "x"
  by (simp_all add: fresh_star_def fresh_Pair lam.fresh fresh_fact)

lemma better_d4_intro:
  assumes a: "t1 \<longrightarrow>d t2" "s1 \<longrightarrow>d s2"
  shows "App (Lam [x].t1) s1 \<longrightarrow>d t2[x::=s2]"
proof -
  obtain y::"name" where fs: "atom y\<sharp>(x,t1,s1,t2,s2)" by (rule obtain_fresh)
  have "App (Lam [x].t1) s1 = App (Lam [y].((y \<leftrightarrow> x)\<bullet>t1)) s1" using fs
    by (auto simp add: Abs1_eq_iff' flip_def fresh_Pair fresh_at_base)
  also have "\<dots> \<longrightarrow>d  ((y \<leftrightarrow> x) \<bullet> t2)[y ::= s2]" using fs a by (auto simp add: Dev.eqvt)
  also have "\<dots> = t2[x::=s2]" using fs by (simp add: subst_rename[symmetric])
  finally show "App (Lam [x].t1) s1 \<longrightarrow>d t2[x::=s2]" by simp
qed

lemma Dev_preserves_fresh:
  fixes x::"name"
  assumes a: "M\<longrightarrow>d N"
  shows "atom x\<sharp>M \<Longrightarrow> atom x\<sharp>N"
  using a
  by (induct, auto simp add: lam.fresh)
     (metis fresh_fact)+

lemma Dev_Lam:
  assumes a: "Lam [x].M \<longrightarrow>d N"
  shows "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>d N'"
proof -
  from a have "atom x \<sharp> Lam [x].M" by (simp add: lam.fresh)
  with a have "atom x \<sharp> N" by (simp add: Dev_preserves_fresh)
  with a show "\<exists>N'. N = Lam [x].N' \<and> M \<longrightarrow>d N'"
    apply (cases rule: Dev.cases)
    apply (auto simp add: Abs1_eq_iff lam.fresh)
    apply (rule_tac x="(atom xa \<rightleftharpoons> atom x) \<bullet> s" in exI)
    apply (auto simp add: fresh_permute_left lam.fresh)
    by (metis swap_commute Dev.eqvt)
qed

lemma Development_existence:
  shows "\<exists>M'. M \<longrightarrow>d M'"
by (nominal_induct M rule: lam.strong_induct)
   (auto dest!: Dev_Lam intro: better_d4_intro)

lemma Triangle:
  assumes a: "t \<longrightarrow>d t1" "t \<longrightarrow>1 t2"
  shows "t2 \<longrightarrow>1 t1"
using a
proof(nominal_induct avoiding: t2 rule: Dev.strong_induct)
  case (d4 x s1 s2 t1 t1' t2)
  have  fc: "atom x\<sharp>t2" "atom x\<sharp>s1" by fact+
  have "App (Lam [x].t1) s1 \<longrightarrow>1 t2" by fact
  then obtain t' s' where reds:
             "(t2 = App (Lam [x].t') s' \<and> t1 \<longrightarrow>1 t' \<and> s1 \<longrightarrow>1 s') \<or>
              (t2 = t'[x::=s'] \<and> t1 \<longrightarrow>1 t' \<and> s1 \<longrightarrow>1 s')"
  using fc by (auto dest!: One_Redex)
  have ih1: "t1 \<longrightarrow>1 t' \<Longrightarrow>  t' \<longrightarrow>1 t1'" by fact
  have ih2: "s1 \<longrightarrow>1 s' \<Longrightarrow>  s' \<longrightarrow>1 s2" by fact
  { assume "t1 \<longrightarrow>1 t'" "s1 \<longrightarrow>1 s'"
    then have "App (Lam [x].t') s' \<longrightarrow>1 t1'[x::=s2]"
      using ih1 ih2 by (auto intro: better_o4_intro)
  }
  moreover
  { assume "t1 \<longrightarrow>1 t'" "s1 \<longrightarrow>1 s'"
    then have "t'[x::=s'] \<longrightarrow>1 t1'[x::=s2]"
      using ih1 ih2 by (auto intro: One_subst)
  }
  ultimately show "t2 \<longrightarrow>1 t1'[x::=s2]" using reds by auto
qed (auto dest!: One_Lam One_Var One_App)

lemma Diamond_for_One:
  assumes a: "t \<longrightarrow>1 t1" "t \<longrightarrow>1 t2"
  shows "\<exists>t3. t2 \<longrightarrow>1 t3 \<and> t1 \<longrightarrow>1 t3"
proof -
  obtain tc where "t \<longrightarrow>d tc" using Development_existence by blast
  with a have "t2 \<longrightarrow>1 tc" and "t1 \<longrightarrow>1 tc" by (simp_all add: Triangle)
  then show "\<exists>t3. t2 \<longrightarrow>1 t3 \<and> t1 \<longrightarrow>1 t3" by blast
qed

lemma Rectangle_for_One:
  assumes a:  "t \<longrightarrow>1* t1" "t \<longrightarrow>1 t2"
  shows "\<exists>t3. t1 \<longrightarrow>1 t3 \<and> t2 \<longrightarrow>1* t3"
using a Diamond_for_One by (induct arbitrary: t2) (blast)+

lemma CR_for_One_star:
  assumes a: "t \<longrightarrow>1* t1" "t \<longrightarrow>1* t2"
    shows "\<exists>t3. t2 \<longrightarrow>1* t3 \<and> t1 \<longrightarrow>1* t3"
using a Rectangle_for_One by (induct arbitrary: t2) (blast)+

section {* Establishing the Equivalence of Beta-star and One-star *}

lemma Beta_Lam_cong:
  assumes a: "t1 \<longrightarrow>b* t2"
  shows "Lam [x].t1 \<longrightarrow>b* Lam [x].t2"
using a by (induct) (blast)+

lemma Beta_App_cong_aux:
  assumes a: "t1 \<longrightarrow>b* t2"
  shows "App t1 s\<longrightarrow>b* App t2 s"
    and "App s t1 \<longrightarrow>b* App s t2"
using a by (induct) (blast)+

lemma Beta_App_cong:
  assumes a: "t1 \<longrightarrow>b* t2" "s1 \<longrightarrow>b* s2"
  shows "App t1 s1 \<longrightarrow>b* App t2 s2"
using a by (blast intro: Beta_App_cong_aux)

lemmas Beta_congs = Beta_Lam_cong Beta_App_cong

lemma One_implies_Beta_star:
  assumes a: "t \<longrightarrow>1 s"
  shows "t \<longrightarrow>b* s"
using a by (induct, auto intro!: Beta_congs)
  (metis (hide_lams, no_types) Beta_App_cong_aux(1) Beta_App_cong_aux(2) Beta_Lam_cong b4 bs2 bs3 fresh_PairD(2))

lemma One_congs:
  assumes a: "t1 \<longrightarrow>1* t2"
  shows "Lam [x].t1 \<longrightarrow>1* Lam [x].t2"
  and   "App t1 s \<longrightarrow>1* App t2 s"
  and   "App s t1 \<longrightarrow>1* App s t2"
using a by (induct) (auto intro: One_refl)

lemma Beta_implies_One_star:
  assumes a: "t1 \<longrightarrow>b t2"
  shows "t1 \<longrightarrow>1* t2"
using a by (induct) (auto intro: One_refl One_congs better_o4_intro)

lemma Beta_star_equals_One_star:
  shows "t1 \<longrightarrow>1* t2 = t1 \<longrightarrow>b* t2"
proof
  assume "t1 \<longrightarrow>1* t2"
  then show "t1 \<longrightarrow>b* t2" by (induct) (auto intro: One_implies_Beta_star)
next
  assume "t1 \<longrightarrow>b* t2"
  then show "t1 \<longrightarrow>1* t2" by (induct) (auto intro: Beta_implies_One_star)
qed

section {* The Church-Rosser Theorem *}

theorem CR_for_Beta_star:
  assumes a: "t \<longrightarrow>b* t1" "t\<longrightarrow>b* t2"
  shows "\<exists>t3. t1 \<longrightarrow>b* t3 \<and> t2 \<longrightarrow>b* t3"
proof -
  from a have "t \<longrightarrow>1* t1" and "t\<longrightarrow>1* t2" by (simp_all add: Beta_star_equals_One_star)
  then have "\<exists>t3. t1 \<longrightarrow>1* t3 \<and> t2 \<longrightarrow>1* t3" by (simp add: CR_for_One_star)
  then show "\<exists>t3. t1 \<longrightarrow>b* t3 \<and> t2 \<longrightarrow>b* t3" by (simp add: Beta_star_equals_One_star)
qed

end
