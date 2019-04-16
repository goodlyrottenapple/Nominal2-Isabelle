header {* Constant definitions *}

theory Consts imports Utils begin

fun Umn :: "nat \<Rightarrow> nat \<Rightarrow> lam"
where
  [simp del]: "Umn 0 n = \<integral>(cn 0). Var (cn n)"
| [simp del]: "Umn (Suc m) n = \<integral>(cn (Suc m)). Umn m n"

lemma [simp]: "2 = Suc 1"
  by auto

lemma split_lemma:
  "(a = b \<and> X) \<or> (a \<noteq> b \<and> Y) \<longleftrightarrow> (a = b \<longrightarrow> X) \<and> (a \<noteq> b \<longrightarrow> Y)"
  by blast

lemma Lam_U:
  assumes "x \<noteq> y" "y \<noteq> z" "x \<noteq> z"
  shows "Umn 2 0 = \<integral>x. \<integral>y. \<integral>z. Var z"
        "Umn 2 1 = \<integral>x. \<integral>y. \<integral>z. Var y"
        "Umn 2 2 = \<integral>x. \<integral>y. \<integral>z. Var x"
  apply (simp_all add: Umn.simps Abs1_eq_iff lam.fresh fresh_at_base flip_def[symmetric] Umn.simps cnd permute_flip_at assms assms[symmetric] split_lemma)
  apply (intro impI conjI)
  apply (metis assms)+
  done

lemma supp_U1: "n \<le> m \<Longrightarrow> atom (cn n) \<notin> supp (Umn m n)"
  by (induct m)
     (auto simp add: lam.supp supp_at_base Umn.simps le_Suc_eq)

lemma supp_U2: "supp (Umn m n) \<subseteq> {atom (cn n)}"
  by (induct m) (auto simp add: lam.supp supp_at_base Umn.simps)

lemma supp_U[simp]: "n \<le> m \<Longrightarrow> supp (Umn m n) = {}"
  using supp_U1 supp_U2
  by blast

lemma U_eqvt:
  "n \<le> m \<Longrightarrow> p \<bullet> (Umn m n) = Umn m n"
  by (rule_tac [!] perm_supp_eq) (simp_all add: fresh_star_def fresh_def)

definition VAR where "VAR \<equiv> \<integral>cx. \<integral>cy. (Var cy \<cdot> (Umn 2 2) \<cdot> Var cx \<cdot> Var cy)"
definition "APP \<equiv> \<integral>cx. \<integral>cy. \<integral>cz. (Var cz \<cdot> Umn 2 1 \<cdot> Var cx \<cdot> Var cy \<cdot> Var cz)"
definition "Abs \<equiv> \<integral>cx. \<integral>cy. (Var cy \<cdot> Umn 2 0 \<cdot> Var cx \<cdot> Var cy)"

lemma VAR_APP_Abs:
  "x \<noteq> e \<Longrightarrow> VAR = \<integral>x. \<integral>e. (Var e \<cdot> Umn 2 2 \<cdot> Var x \<cdot> Var e)"
  "e \<noteq> x \<Longrightarrow> e \<noteq> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> APP = \<integral>x. \<integral>y. \<integral>e. (Var e \<cdot> Umn 2 1 \<cdot> Var x \<cdot> Var y \<cdot> Var e)"
  "x \<noteq> e \<Longrightarrow> Abs = \<integral>x. \<integral>e. (Var e \<cdot> Umn 2 0 \<cdot> Var x \<cdot> Var e)"
  unfolding VAR_def APP_def Abs_def
  by (simp_all add: Abs1_eq_iff lam.fresh flip_def[symmetric] U_eqvt fresh_def lam.supp supp_at_base split_lemma permute_flip_at)
     (auto simp only: cx_cy_cz cx_cy_cz[symmetric])

lemma VAR_app:
  "VAR \<cdot> x \<cdot> e \<approx> e \<cdot> Umn 2 2 \<cdot> x \<cdot> e"
  by (rule lam2_fast_app[OF VAR_APP_Abs(1)]) simp_all

lemma APP_app:
  "APP \<cdot> x \<cdot> y \<cdot> e \<approx> e \<cdot> Umn 2 1 \<cdot> x \<cdot> y \<cdot> e"
  by (rule lam3_fast_app[OF VAR_APP_Abs(2)]) (simp_all)

lemma Abs_app:
  "Abs \<cdot> x \<cdot> e \<approx> e \<cdot> Umn 2 0 \<cdot> x \<cdot> e"
  by (rule lam2_fast_app[OF VAR_APP_Abs(3)]) simp_all

lemma supp_VAR_APP_Abs[simp]:
  "supp VAR = {}" "supp APP = {}" "supp Abs = {}"
  by (simp_all add: VAR_def APP_def Abs_def lam.supp supp_at_base) blast+

lemma VAR_APP_Abs_eqvt[eqvt]:
  "p \<bullet> VAR = VAR" "p \<bullet> APP = APP" "p \<bullet> Abs = Abs"
  by (rule_tac [!] perm_supp_eq) (simp_all add: fresh_star_def fresh_def)

nominal_function
  Numeral :: "lam \<Rightarrow> lam" ("\<lbrace>_\<rbrace>" 1000)
where
  "\<lbrace>Var x\<rbrace> = VAR \<cdot> (Var x)"
| Ap: "\<lbrace>M \<cdot> N\<rbrace> = APP \<cdot> \<lbrace>M\<rbrace> \<cdot> \<lbrace>N\<rbrace>"
| "\<lbrace>\<integral>x. M\<rbrace> = Abs \<cdot> (\<integral>x. \<lbrace>M\<rbrace>)"
proof auto
  fix x :: lam and P
  assume "\<And>xa. x = Var xa \<Longrightarrow> P" "\<And>M N. x = M \<cdot> N \<Longrightarrow> P" "\<And>xa M. x = \<integral> xa. M \<Longrightarrow> P"
  then show "P"
    by (rule_tac y="x" and c="0 :: perm" in lam.strong_exhaust)
       (auto simp add: Abs1_eq_iff fresh_star_def)[3]
next
  fix x :: name and M and xa :: name and Ma
  assume "[[atom x]]lst. M = [[atom xa]]lst. Ma"
    "eqvt_at Numeral_sumC M"
  then show "[[atom x]]lst. Numeral_sumC M = [[atom xa]]lst. Numeral_sumC Ma"
    apply -
    apply (erule Abs_lst1_fcb)
    apply (simp_all add: Abs_fresh_iff)
    apply (erule fresh_eqvt_at)
    apply (simp_all add: finite_supp Abs1_eq_iff eqvt_at_def)
    done
next
  show "eqvt Numeral_graph" unfolding eqvt_def Numeral_graph_def
    by (rule, perm_simp, rule)
qed

nominal_termination (eqvt) by lexicographic_order

lemma supp_numeral[simp]:
  "supp \<lbrace>x\<rbrace> = supp x"
  by (induct x rule: lam.induct)
     (simp_all add: lam.supp)

lemma fresh_numeral[simp]:
  "x \<sharp> \<lbrace>y\<rbrace> = x \<sharp> y"
  unfolding fresh_def by simp

fun app_lst :: "name \<Rightarrow> lam list \<Rightarrow> lam" where
  "app_lst n [] = Var n"
| "app_lst n (h # t) = (app_lst n t) \<cdot> h"

lemma app_lst_eqvt[eqvt]: "p \<bullet> (app_lst t ts) = app_lst (p \<bullet> t) (p \<bullet> ts)"
  by (induct ts arbitrary: t p) (simp_all add: eqvts)

lemma supp_app_lst: "supp (app_lst x l) = {atom x} \<union> supp l"
  apply (induct l)
  apply (simp_all add: supp_Nil lam.supp supp_at_base supp_Cons)
  by blast

lemma app_lst_eq_iff: "app_lst n M = app_lst n N \<Longrightarrow> M = N"
  by (induct M N rule: list_induct2') simp_all

lemma app_lst_rev_eq_iff: "app_lst n (rev M) = app_lst n (rev N) \<Longrightarrow> M = N"
  by (drule app_lst_eq_iff) simp

nominal_function
  Ltgt :: "lam list \<Rightarrow> lam" ("\<guillemotleft>_\<guillemotright>" 1000)
where
  [simp del]: "atom x \<sharp> l \<Longrightarrow> \<guillemotleft>l\<guillemotright> = \<integral>x. (app_lst x (rev l))"
  unfolding eqvt_def Ltgt_graph_def
  apply (rule, perm_simp, rule, rule)
  apply (rule_tac x="x" and ?'a="name" in obtain_fresh)
  apply (simp_all add: Abs1_eq_iff lam.fresh swap_fresh_fresh fresh_at_base)
  apply (simp add: eqvts swap_fresh_fresh)
  apply (case_tac "x = xa")
  apply simp_all
  apply (subgoal_tac "eqvt app_lst")
  apply (erule fresh_fun_eqvt_app2)
  apply (simp_all add: fresh_at_base lam.fresh eqvt_def eqvts_raw fresh_rev)
  done

nominal_termination (eqvt) by lexicographic_order

lemma ltgt_eq_iff[simp]:
  "\<guillemotleft>M\<guillemotright> = \<guillemotleft>N\<guillemotright> \<longleftrightarrow> M = N"
proof auto
  obtain x :: name where "atom x \<sharp> (M, N)" using obtain_fresh by auto
  then have *: "atom x \<sharp> M" "atom x \<sharp> N" using fresh_Pair by simp_all
  then show "(\<guillemotleft>M\<guillemotright> = \<guillemotleft>N\<guillemotright>) \<Longrightarrow> (M = N)" by (simp add: Abs1_eq_iff app_lst_rev_eq_iff Ltgt.simps)
qed

lemma Ltgt1_app: "\<guillemotleft>[M]\<guillemotright> \<cdot> N \<approx> N \<cdot> M"
proof -
  obtain x :: name where "atom x \<sharp> (M, N)" using obtain_fresh by auto
  then have "atom x \<sharp> M" "atom x \<sharp> N" using fresh_Pair by simp_all
  then show ?thesis
  apply (subst Ltgt.simps)
  apply (simp add: fresh_Cons fresh_Nil)
  apply (rule b3, rule bI, simp add: b1)
  done
qed

lemma Ltgt3_app: "\<guillemotleft>[M,N,P]\<guillemotright> \<cdot> R \<approx> R \<cdot> M \<cdot> N \<cdot> P"
proof -
  obtain x :: name where "atom x \<sharp> (M, N, P, R)" using obtain_fresh by auto
  then have *: "atom x \<sharp> (M,N,P)" "atom x \<sharp> R" using fresh_Pair by simp_all
  then have s: "Var x \<cdot> M \<cdot> N \<cdot> P [x ::= R] \<approx> R \<cdot> M \<cdot> N \<cdot> P" using b1 by simp
  show ?thesis using *
    apply (subst Ltgt.simps)
  apply (simp add: fresh_Cons fresh_Nil fresh_Pair_elim)
  apply auto[1]
  apply (rule b3, rule bI, simp add: b1)
  done
qed

lemma supp_ltgt[simp]:
  "supp \<guillemotleft>t\<guillemotright> = supp t"
proof -
  obtain x :: name where *:"atom x \<sharp> t" using obtain_fresh by auto
  show ?thesis using *
  by (simp_all add: Ltgt.simps lam.supp supp_at_base supp_Nil supp_app_lst supp_rev fresh_def)
qed

lemma fresh_ltgt[simp]:
  "x \<sharp> \<guillemotleft>[y]\<guillemotright> = x \<sharp> y"
  "x \<sharp> \<guillemotleft>[t,r,s]\<guillemotright> = x \<sharp> (t,r,s)"
  by (simp_all add: fresh_def supp_Cons supp_Nil supp_Pair)

lemma Ltgt1_subst[simp]:
  "\<guillemotleft>[M]\<guillemotright> [y ::= A] = \<guillemotleft>[M [y ::= A]]\<guillemotright>"
proof -
  obtain x :: name where a: "atom x \<sharp> (M, A, y, M [y ::= A])" using obtain_fresh by blast
  have "x \<noteq> y" using a[simplified fresh_Pair fresh_at_base] by simp
  then show ?thesis
    apply (subst Ltgt.simps)
    using a apply (simp add: fresh_Nil fresh_Cons fresh_Pair_elim)
    apply (subst Ltgt.simps)
    using a apply (simp add: fresh_Pair_elim fresh_Nil fresh_Cons)
    apply (simp add: a)
    done
qed

lemma U_app:
  "\<guillemotleft>[A,B,C]\<guillemotright> \<cdot> Umn 2 2 \<approx> A" "\<guillemotleft>[A,B,C]\<guillemotright> \<cdot> Umn 2 1 \<approx> B" "\<guillemotleft>[A,B,C]\<guillemotright> \<cdot> Umn 2 0 \<approx> C"
  by (rule b3, rule Ltgt3_app, rule lam3_fast_app, rule Lam_U, simp_all)
     (rule b3, rule Ltgt3_app, rule lam3_fast_app, rule Lam_U[simplified], simp_all)+

definition "F1 \<equiv> \<integral>cx. (APP \<cdot> \<lbrace>VAR\<rbrace> \<cdot> (VAR \<cdot> Var cx))"
definition "F2 \<equiv> \<integral>cx. \<integral>cy. \<integral>cz. ((APP \<cdot> (APP \<cdot> \<lbrace>APP\<rbrace> \<cdot> (Var cz \<cdot> Var cx))) \<cdot> (Var cz \<cdot> Var cy))"
definition "F3 \<equiv> \<integral>cx. \<integral>cy. (APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> (\<integral>cz. (Var cy \<cdot> (Var cx \<cdot> Var cz)))))"


lemma Lam_F:
  "F1 = \<integral>x. (APP \<cdot> \<lbrace>VAR\<rbrace> \<cdot> (VAR \<cdot> Var x))"
  "a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow> c \<noteq> b \<Longrightarrow> F2 = \<integral>a. \<integral>b. \<integral>c. ((APP \<cdot> (APP \<cdot> \<lbrace>APP\<rbrace> \<cdot> (Var c \<cdot> Var a))) \<cdot> (Var c \<cdot> Var b))"
  "a \<noteq> b \<Longrightarrow> a \<noteq> x \<Longrightarrow> x \<noteq> b \<Longrightarrow> F3 = \<integral>a. \<integral>b. (APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> (\<integral>x. (Var b \<cdot> (Var a \<cdot> Var x)))))"
  by (simp_all add: F1_def F2_def F3_def Abs1_eq_iff lam.fresh supp_at_base VAR_APP_Abs_eqvt Numeral.eqvt flip_def[symmetric] fresh_at_base split_lemma permute_flip_at)
     (auto simp add: cx_cy_cz cx_cy_cz[symmetric])

lemma supp_F[simp]:
  "supp F1 = {}" "supp F2 = {}" "supp F3 = {}"
  by (simp_all add: F1_def F2_def F3_def lam.supp supp_at_base)
     blast+

lemma F_eqvt[eqvt]:
  "p \<bullet> F1 = F1" "p \<bullet> F2 = F2" "p \<bullet> F3 = F3"
  by (rule_tac [!] perm_supp_eq)
     (simp_all add: fresh_star_def fresh_def)

lemma F_app:
  "F1 \<cdot> A \<approx> APP \<cdot> \<lbrace>VAR\<rbrace> \<cdot> (VAR \<cdot> A)"
  "F2 \<cdot> A \<cdot> B \<cdot> C \<approx> (APP \<cdot> (APP \<cdot> \<lbrace>APP\<rbrace> \<cdot> (C \<cdot> A))) \<cdot> (C \<cdot> B)"
  by (rule lam1_fast_app, rule Lam_F, simp_all)
     (rule lam3_fast_app, rule Lam_F, simp_all)

lemma F3_app:
  assumes f: "atom x \<sharp> A" "atom x \<sharp> B" (* or A and B have empty support *)
  shows "F3 \<cdot> A \<cdot> B \<approx> APP \<cdot> \<lbrace>Abs\<rbrace> \<cdot> (Abs \<cdot> (\<integral>x. (B \<cdot> (A \<cdot> Var x))))"
proof -
  obtain y :: name where b: "atom y \<sharp> (x, A, B)" using obtain_fresh by blast
  obtain z :: name where c: "atom z \<sharp> (x, y, A, B)" using obtain_fresh by blast
  have *: "x \<noteq> z" "x \<noteq> y" "y \<noteq> z"
    using b c by (simp_all add: fresh_Pair fresh_at_base) blast+
  have **:
    "atom y \<sharp> z" "atom x \<sharp> z" "atom y \<sharp> x"
    "atom z \<sharp> y" "atom z \<sharp> x" "atom x \<sharp> y"
    "atom x \<sharp> A" "atom y \<sharp> A" "atom z \<sharp> A"
    "atom x \<sharp> B" "atom y \<sharp> B" "atom z \<sharp> B"
    using b c f by (simp_all add: fresh_Pair fresh_at_base) blast+
  show ?thesis
    apply (simp add: Lam_F(3)[of y z x] * *[symmetric])
    apply (rule b3) apply (rule b5) apply (rule bI)
    apply (simp add: ** fresh_Pair * *[symmetric])
    apply (rule b3) apply (rule bI)
    apply (simp add: ** fresh_Pair * *[symmetric])
    apply (rule b1)
    done
qed

definition Lam_A1_pre : "A1 \<equiv> \<integral>cx. \<integral>cy. (F1 \<cdot> Var cx)"
definition Lam_A2_pre : "A2 \<equiv> \<integral>cx. \<integral>cy. \<integral>cz. (F2 \<cdot> Var cx \<cdot> Var cy \<cdot> \<guillemotleft>[Var cz]\<guillemotright>)"
definition Lam_A3_pre : "A3 \<equiv> \<integral>cx. \<integral>cy. (F3 \<cdot> Var cx \<cdot> \<guillemotleft>[Var cy]\<guillemotright>)"
lemma Lam_A:
  "x \<noteq> y \<Longrightarrow> A1 = \<integral>x. \<integral>y. (F1 \<cdot> Var x)"
  "a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow> c \<noteq> b \<Longrightarrow> A2 = \<integral>a. \<integral>b. \<integral>c. (F2 \<cdot> Var a \<cdot> Var b \<cdot> \<guillemotleft>[Var c]\<guillemotright>)"
  "a \<noteq> b \<Longrightarrow> A3 = \<integral>a. \<integral>b. (F3 \<cdot> Var a \<cdot> \<guillemotleft>[Var b]\<guillemotright>)"
  by (simp_all add: Lam_A1_pre Lam_A2_pre Lam_A3_pre Abs1_eq_iff lam.fresh supp_at_base VAR_APP_Abs_eqvt Numeral.eqvt flip_def[symmetric] fresh_at_base F_eqvt Ltgt.eqvt split_lemma permute_flip_at cx_cy_cz cx_cy_cz[symmetric])
     auto

lemma supp_A[simp]:
  "supp A1 = {}" "supp A2 = {}" "supp A3 = {}"
  by (auto simp add: Lam_A1_pre Lam_A2_pre Lam_A3_pre lam.supp supp_at_base supp_Cons supp_Nil)

lemma A_app:
  "A1 \<cdot> A \<cdot> B \<approx> F1 \<cdot> A"
  "A2 \<cdot> A \<cdot> B \<cdot> C \<approx> F2 \<cdot> A \<cdot> B \<cdot> \<guillemotleft>[C]\<guillemotright>"
  "A3 \<cdot> A \<cdot> B \<approx> F3 \<cdot> A \<cdot> \<guillemotleft>[B]\<guillemotright>"
  apply (rule lam2_fast_app, rule Lam_A, simp_all)
  apply (rule lam3_fast_app, rule Lam_A, simp_all)
  apply (rule lam2_fast_app, rule Lam_A, simp_all)
  done

definition "NUM \<equiv> \<guillemotleft>[\<guillemotleft>[A1,A2,A3]\<guillemotright>]\<guillemotright>"

lemma supp_NUM[simp]:
  "supp NUM = {}"
  by (auto simp only: NUM_def supp_ltgt supp_Pair supp_A supp_Cons supp_Nil)

end
