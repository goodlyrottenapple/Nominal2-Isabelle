theory BetaCR
imports CR
begin

(* TODO1: Does not work:*)

(* equivariance beta_star *)

(* proved manually below. *)

lemma eqvt_helper: "x1 \<longrightarrow>b* x2 \<Longrightarrow>  (p \<bullet> x1) \<longrightarrow>b* (p \<bullet> x2)"
  by (erule beta_star.induct)
     (metis beta.eqvt bs2 bs1)+

lemma [eqvt]: "p \<bullet> (x1 \<longrightarrow>b* x2) = ((p \<bullet> x1) \<longrightarrow>b* (p \<bullet> x2))"
  apply rule
  apply (drule permute_boolE)
  apply (erule eqvt_helper)
  apply (intro permute_boolI)
  apply (drule_tac p="-p" in eqvt_helper)
  by simp

definition
  equ :: "lam \<Rightarrow> lam \<Rightarrow> bool" ("_ \<approx> _")
where
  "t \<approx> s \<longleftrightarrow> (\<exists>r. t \<longrightarrow>b* r \<and> s \<longrightarrow>b* r)"

lemma equ_refl:
  shows "t \<approx> t"
  unfolding equ_def by auto

lemma equ_sym:
  assumes "t \<approx> s"
  shows "s \<approx> t"
  using assms unfolding equ_def
  by auto

lemma equ_trans:
  assumes "A \<approx> B" "B \<approx> C"
  shows "A \<approx> C"
  using assms unfolding equ_def
proof (elim exE conjE)
  fix D E
  assume a: "A \<longrightarrow>b* D" "B \<longrightarrow>b* D" "B \<longrightarrow>b* E" "C \<longrightarrow>b* E"
  then obtain F where "D \<longrightarrow>b* F" "E \<longrightarrow>b* F" using CR_for_Beta_star by blast
  then have "A \<longrightarrow>b* F \<and> C \<longrightarrow>b* F" using a bs3 by blast
  then show "\<exists>F. A \<longrightarrow>b* F \<and> C \<longrightarrow>b* F" by blast
qed

lemma App_beta: "A \<longrightarrow>b* B \<Longrightarrow> C \<longrightarrow>b* D \<Longrightarrow> App A C \<longrightarrow>b* App B D"
  apply (erule beta_star.induct)
  apply auto
  apply (erule beta_star.induct)
  apply auto
  done

lemma Lam_beta: "A \<longrightarrow>b* B \<Longrightarrow> Lam [x]. A \<longrightarrow>b* Lam [x]. B"
  by (erule beta_star.induct) auto

lemma Lam_rsp: "A \<approx> B \<Longrightarrow> Lam [x]. A \<approx> Lam [x]. B"
  unfolding equ_def
  apply auto
  apply (rule_tac x="Lam [x]. r" in exI)
  apply (auto simp add: Lam_beta)
  done

lemma [quot_respect]:
  shows "(op = ===> equ) Var Var"
  and   "(equ ===> equ ===> equ) App App"
  and   "(op = ===> equ ===> equ) CR.Lam CR.Lam"
  unfolding fun_rel_def equ_def
  apply auto
  apply (rule_tac x="App r ra" in exI)
  apply (auto simp add: App_beta)
  apply (rule_tac x="Lam [x]. r" in exI)
  apply (auto simp add: Lam_beta)
  done

lemma beta_subst1_pre: "B \<longrightarrow>b C \<Longrightarrow> A [x ::= B] \<longrightarrow>b* A [x ::= C]"
  by (nominal_induct A avoiding: x B C rule: lam.strong_induct)
     (auto simp add: App_beta Lam_beta)

lemma beta_subst1: "B \<longrightarrow>b* C \<Longrightarrow> A [x ::= B] \<longrightarrow>b* A [x ::= C]"
  apply (erule beta_star.induct)
  apply auto
  apply (subgoal_tac "A [x ::= M2] \<longrightarrow>b* A [x ::= M3]")
  apply (rotate_tac 1)
  apply (erule bs3)
  apply assumption
  apply (simp add: beta_subst1_pre)
  done

lemma beta_subst2_pre:
  assumes "A \<longrightarrow>b B" shows "A [x ::= C] \<longrightarrow>b* B [x ::= C]"
  using assms
  apply (nominal_induct avoiding: x C rule: beta.strong_induct)
  apply (auto simp add: App_beta fresh_star_def fresh_Pair Lam_beta)[3]
  apply (subst substitution_lemma)
  apply (auto simp add: fresh_star_def fresh_Pair fresh_at_base)[2]
  apply (auto simp add: fresh_star_def fresh_Pair)
  apply (rule beta_star.intros)
  defer
  apply (subst beta.intros)
  apply (auto simp add: fresh_fact)
  done

lemma beta_subst2: "A \<longrightarrow>b* B \<Longrightarrow> A [x ::= C] \<longrightarrow>b* B [x ::= C]"
  apply (erule beta_star.induct)
  apply auto
  apply (subgoal_tac "M2[x ::= C] \<longrightarrow>b* M3[x ::= C]")
  apply (rotate_tac 1)
  apply (erule bs3)
  apply assumption
  apply (simp add: beta_subst2_pre)
  done

lemma beta_subst: "A \<longrightarrow>b* B \<Longrightarrow> C \<longrightarrow>b* D \<Longrightarrow> A [x ::= C] \<longrightarrow>b* B [x ::= D]"
  using beta_subst1 beta_subst2 bs3 by metis

lemma subst_rsp_pre:
  "x \<approx> y \<Longrightarrow> xb \<approx> ya \<Longrightarrow> x [xa ::= xb] \<approx> y [xa ::= ya]"
  unfolding equ_def
  apply auto
  apply (rule_tac x="r [xa ::= ra]" in exI)
  apply (simp add: beta_subst)
  done

lemma [quot_respect]:
  shows "(equ ===> op = ===> equ ===> equ) subst subst"
unfolding fun_rel_def by (auto simp add: subst_rsp_pre)

lemma [quot_respect]:
  shows "(op = ===> equ ===> equ) permute permute"
  unfolding fun_rel_def equ_def
  apply (auto intro: eqvts)
  apply (rule_tac x="x \<bullet> r" in exI)
  using eqvts(1) permute_boolI by metis

quotient_type qlam = lam / equ
  by (auto intro!: equivpI reflpI sympI transpI simp add: equ_refl equ_sym)
     (erule equ_trans, assumption)

quotient_definition "QVar::name \<Rightarrow> qlam" is Var
quotient_definition "QApp::qlam \<Rightarrow> qlam \<Rightarrow> qlam" is App
quotient_definition QLam ("QLam [_]._")
  where "QLam::name \<Rightarrow> qlam \<Rightarrow> qlam" is CR.Lam

lemmas qlam_strong_induct = lam.strong_induct[quot_lifted]
lemmas qlam_induct = lam.induct[quot_lifted]

instantiation qlam :: pt
begin

quotient_definition "permute_qlam::perm \<Rightarrow> qlam \<Rightarrow> qlam" 
  is "permute::perm \<Rightarrow> lam \<Rightarrow> lam"

instance
apply default
apply(descending)
apply(simp)
apply(rule equ_refl)
apply(descending)
apply(simp)
apply(rule equ_refl)
done

end

lemma qlam_perm[simp, eqvt]:
  shows "p \<bullet> (QVar x) = QVar (p \<bullet> x)"
  and "p \<bullet> (QApp t s) = QApp (p \<bullet> t) (p \<bullet> s)"
  and "p \<bullet> (QLam [x].t) = QLam [p \<bullet> x].(p \<bullet> t)"
  by(descending, simp add: equ_refl)+

lemma qlam_supports:
  shows "{atom x} supports (QVar x)"
  and   "supp (t, s) supports (QApp t s)"
  and   "supp (x, t) supports (QLam [x].t)"
unfolding supports_def fresh_def[symmetric]
by (auto simp add: swap_fresh_fresh)

lemma qlam_fs:
  fixes t::"qlam"
  shows "finite (supp t)"
apply(induct t rule: qlam_induct)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp add: supp_Pair)
apply(rule supports_finite)
apply(rule qlam_supports)
apply(simp add: supp_Pair finite_supp)
done

instantiation qlam :: fs
begin

instance
apply(default)
apply(rule qlam_fs)
done

end

quotient_definition subst_qlam ("_[_ ::q= _]")
  where "subst_qlam::qlam \<Rightarrow> name \<Rightarrow> qlam \<Rightarrow> qlam" is subst  

definition
  "Supp t = \<Inter>{supp s | s. s \<approx> t}"

lemma Supp_rsp:
  "a \<approx> b \<Longrightarrow> Supp a = Supp b"
  unfolding Supp_def
  apply(rule_tac f="Inter" in arg_cong)
  apply(auto)
  apply (metis equ_trans)
  by (metis equivp_def qlam_equivp)

lemma [quot_respect]:
  shows "(equ ===> op=) Supp Supp"
  unfolding fun_rel_def by (auto simp add: Supp_rsp)

quotient_definition "supp_qlam::qlam \<Rightarrow> atom set" 
  is "Supp::lam \<Rightarrow> atom set"

lemma Supp_supp:
  "Supp t \<subseteq> supp t"
unfolding Supp_def
apply(auto)
apply(drule_tac x="supp t" in spec)
apply(auto simp add: equ_refl)
done

lemma supp_subst:
  shows "supp (t[x ::= s]) \<subseteq> (supp t - {atom x}) \<union> supp s"
  by (induct t x s rule: subst.induct) (auto simp add: lam.supp supp_at_base)

lemma supp_beta: "x \<longrightarrow>b r \<Longrightarrow> supp r \<subseteq> supp x"
  apply (induct rule: beta.induct)
  apply (simp_all add: lam.supp)
  apply blast+
  using supp_subst by blast

lemma supp_beta_star: "x \<longrightarrow>b* r \<Longrightarrow> supp r \<subseteq> supp x"
  apply (erule beta_star.induct)
  apply auto
  using supp_beta by blast

lemma supp_equ: "x \<approx> y \<Longrightarrow> \<exists>z. z \<approx> x \<and> supp z \<subseteq> supp x \<inter> supp y"
  unfolding equ_def
  apply (simp (no_asm) only: equ_def[symmetric])
  apply (elim exE)
  apply (rule_tac x=r in exI)
  apply rule
  apply (metis bs1 equ_def)
  using supp_beta_star by blast

lemma supp_psubset: "Supp x \<subset> supp x \<Longrightarrow> \<exists>t. t \<approx> x \<and> supp t \<subset> supp x"
proof -
  assume "Supp x \<subset> supp x"
  then obtain a where "a \<in> supp x" "a \<notin> Supp x" by blast
  then obtain y where nin: "y \<approx> x" "a \<notin> supp y" unfolding Supp_def by blast
  then obtain t where eq: "t \<approx> x" "supp t \<subseteq> supp x \<inter> supp y"
    using supp_equ equ_sym by blast
  then have "supp t \<subset> supp x" using nin
    by (metis `(a\<Colon>atom) \<in> supp (x\<Colon>lam)` le_infE psubset_eq set_rev_mp)
  then show "\<exists>t. t \<approx> x \<and> supp t \<subset> supp x" using eq by blast
qed

lemma Supp_exists: "\<exists>t. supp t = Supp t \<and> t \<approx> x"
proof -
  have "\<And>fs x. supp x = fs \<Longrightarrow> \<exists>t. supp t = Supp t \<and> t \<approx> x"
  proof -
    fix fs
    show "\<And>x. supp x = fs \<Longrightarrow> \<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x"
    proof (cases "finite fs")
      case True
      assume fs: "finite fs"
      then show "\<And>x. supp x = fs \<Longrightarrow> \<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x"
      proof (induct fs rule: finite_psubset_induct, clarify)
        fix A :: "atom set" fix x :: lam
        assume IH: "\<And>B xa. \<lbrakk>B \<subset> supp x; supp xa = B\<rbrakk> \<Longrightarrow> \<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> xa"
        show "\<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x"
        proof (cases "supp x = Supp x")
          assume "supp x = Supp x"
          then show "\<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x"
            by (rule_tac x="x" in exI) (simp add: equ_refl)
        next
          assume "supp x \<noteq> Supp x"
          then have "Supp x \<subset> supp x" using Supp_supp by blast
          then obtain y where a1: "supp y \<subset> supp x" "y \<approx> x"
            using supp_psubset by blast
          then obtain t where "supp t = Supp t \<and> t \<approx> y"
            using IH[of "supp y" y] by blast
          then show "\<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x" using a1 equ_trans
            by blast
        qed
      qed
    next
      case False
      fix x :: lam
      assume "supp x = fs" "infinite fs"
      then show "\<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x"
        by (auto simp add: finite_supp)
    qed simp
  qed
  then show "\<exists>t\<Colon>lam. supp t = Supp t \<and> t \<approx> x" by blast
qed

lemma subst3: "x \<noteq> y \<and> atom x \<notin> Supp s \<Longrightarrow> Lam [x]. t [y ::= s] \<approx> Lam [x]. (t [y ::= s])"
proof -
  assume as: "x \<noteq> y \<and> atom x \<notin> Supp s"
  obtain s' where s: "supp s' = Supp s'" "s' \<approx> s" using Supp_exists[of s] by blast
  then have lhs: "Lam [x]. t [y ::= s] \<approx> Lam [x]. t [y ::= s']" using subst_rsp_pre equ_refl equ_sym by blast
  have supp: "Supp s' = Supp s" using Supp_rsp s(2) by blast
  have lhs_rhs: "Lam [x]. t [y ::= s'] = Lam [x]. (t [y ::= s'])"
    by (simp add: fresh_def supp_Pair s supp as supp_at_base)
  have "t [y ::= s'] \<approx> t [y ::= s]"
    using subst_rsp_pre[OF equ_refl s(2)] .
  with Lam_rsp have rhs: "Lam [x]. (t [y ::= s']) \<approx> Lam [x]. (t [y ::= s])" .
  show ?thesis 
    using lhs[unfolded lhs_rhs] rhs equ_trans by blast
qed

thm subst3[quot_lifted]

lemma Supp_Lam:
  "atom a \<notin> Supp (Lam [a].t)"
proof -
  have "atom a \<notin> supp (Lam [a].t)" by (simp add: lam.supp)
  then show ?thesis using Supp_supp
    by blast
qed

lemma [eqvt]: "(p \<bullet> (a \<approx> b)) = ((p \<bullet> a) \<approx> (p \<bullet> b))"
  unfolding equ_def
  by perm_simp rule

lemma [eqvt]: "p \<bullet> (Supp x) = Supp (p \<bullet> x)"
  unfolding Supp_def
  by perm_simp rule

lemmas s = Supp_Lam[quot_lifted]

lemma var_beta_pre: "s \<longrightarrow>b* r \<Longrightarrow> s = Var name \<Longrightarrow> r = Var name"
  apply (induct rule: beta_star.induct)
  apply simp
  apply (subgoal_tac "M2 = Var name")
  apply (thin_tac "M1 \<longrightarrow>b* M2")
  apply (thin_tac "M1 = Var name")
  apply (thin_tac "M1 = Var name \<Longrightarrow> M2 = Var name")
  defer
  apply simp
  apply (erule_tac beta.cases)
  apply simp_all
  done

lemma var_beta: "Var name \<longrightarrow>b* r \<longleftrightarrow> r = Var name"
  by (auto simp add: var_beta_pre)

lemma qlam_eq_iff:
  "(QVar n = QVar m) = (n = m)"
  apply descending unfolding equ_def var_beta by auto

lemma "supp (QVar n) = {atom n}"
  unfolding supp_def
  apply simp
  unfolding qlam_eq_iff
  apply (fold supp_def)
  apply (simp add: supp_at_base)
  done

end



