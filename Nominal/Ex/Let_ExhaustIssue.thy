theory Let
imports "../Nominal2" 
begin


atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Lam x::"name" t::"trm"  binds  x in t
| Let as::"assn" t::"trm"   binds "bn as" in t
and assn =
  ANil
| ACons "name" "trm" "assn"
binder
  bn
where
  "bn ANil = []"
| "bn (ACons x t as) = (atom x) # (bn as)"

lemma alpha_bn_inducts_raw:
  "\<lbrakk>alpha_bn_raw a b; P3 ANil_raw ANil_raw;
 \<And>trm_raw trm_rawa assn_raw assn_rawa name namea.
    \<lbrakk>alpha_trm_raw trm_raw trm_rawa; alpha_bn_raw assn_raw assn_rawa;
     P3 assn_raw assn_rawa\<rbrakk>
    \<Longrightarrow> P3 (ACons_raw name trm_raw assn_raw)
        (ACons_raw namea trm_rawa assn_rawa)\<rbrakk> \<Longrightarrow> P3 a b"
  by (erule alpha_trm_raw_alpha_assn_raw_alpha_bn_raw.inducts(3)[of _ _ "\<lambda>x y. True" _ "\<lambda>x y. True", simplified]) auto

lemmas alpha_bn_inducts = alpha_bn_inducts_raw[quot_lifted]

lemma alpha_bn_refl: "alpha_bn x x"
  by (induct x rule: trm_assn.inducts(2))
     (rule TrueI, auto simp add: trm_assn.eq_iff)

lemma max_eqvt[eqvt]: "p \<bullet> (max (a :: _ :: pure) b) = max (p \<bullet> a) (p \<bullet> b)"
  by (simp add: permute_pure)

lemma what_we_would_like:
  assumes a: "alpha_bn as asa"
  shows "\<forall>p. set (bn as) \<sharp>* fv_bn as \<and> set (bn asa) \<sharp>* fv_bn asa \<and>
   p \<bullet> bn as = bn asa \<and> supp p \<subseteq> set (bn as) \<union> set (bn asa) \<longrightarrow> p \<bullet> as = asa"
  apply (rule alpha_bn_inducts[OF a])
  apply
 (simp_all add: trm_assn.bn_defs trm_assn.perm_bn_simps trm_assn.supp)
 apply clarify
 apply simp
 apply (simp add: atom_eqvt)
 apply (case_tac "name = namea")
 sorry

lemma Abs_lst_fcb2:
  fixes as bs :: "'a :: fs"
    and x y :: "'b :: fs"
    and c::"'c::fs"
  assumes eq: "[ba as]lst. x = [ba bs]lst. y"
  and fcb1: "set (ba as) \<sharp>* f as x c"
  and fresh1: "set (ba as) \<sharp>* c"
  and fresh2: "set (ba bs) \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f as x c) = f (p \<bullet> as) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f bs y c) = f (p \<bullet> bs) (p \<bullet> y) c"
  and ba_inj: "\<And>q r. q \<bullet> ba as = r \<bullet> ba bs \<Longrightarrow> q \<bullet> as = r \<bullet> bs"
  shows "f as x c = f bs y c"
sorry

nominal_function
    height_trm :: "trm \<Rightarrow> nat"
and height_assn :: "assn \<Rightarrow> nat"
where
  "height_trm (Var x) = 1"
| "height_trm (App l r) = max (height_trm l) (height_trm r)"
| "height_trm (Lam v b) = 1 + (height_trm b)"
| "set (bn as) \<sharp>* fv_bn as \<Longrightarrow> height_trm (Let as b) = max (height_assn as) (height_trm b)"
| "height_assn ANil = 0"
| "height_assn (ACons v t as) = max (height_trm t) (height_assn as)"
  apply (simp only: eqvt_def height_trm_height_assn_graph_def)
  apply (rule, perm_simp, rule, rule TrueI)
  apply (case_tac x)
  apply (rule_tac y="a" in trm_assn.strong_exhaust(1))
  apply (auto)[4]
  apply (drule_tac x="assn" in meta_spec)
  apply (drule_tac x="trm" in meta_spec)
  apply (simp add: alpha_bn_refl)
--"HERE"
  defer
  apply (case_tac b rule: trm_assn.exhaust(2))
  apply (auto)[2]
  apply(simp_all)
  apply (erule_tac c="()" in Abs_lst_fcb2)
  apply (simp_all add: pure_fresh fresh_star_def)[3]
  apply (simp add: eqvt_at_def)
  apply (simp add: eqvt_at_def)
  apply assumption
  apply(erule conjE)
  apply (simp add: meta_eq_to_obj_eq[OF height_trm_def, symmetric, unfolded fun_eq_iff])
  apply (simp add: meta_eq_to_obj_eq[OF height_assn_def, symmetric, unfolded fun_eq_iff])
  apply (subgoal_tac "eqvt_at height_assn as")
  apply (subgoal_tac "eqvt_at height_assn asa")
  apply (subgoal_tac "eqvt_at height_trm b")
  apply (subgoal_tac "eqvt_at height_trm ba")
  apply (thin_tac "eqvt_at height_trm_height_assn_sumC (Inr as)")
  apply (thin_tac "eqvt_at height_trm_height_assn_sumC (Inr asa)")
  apply (thin_tac "eqvt_at height_trm_height_assn_sumC (Inl b)")
  apply (thin_tac "eqvt_at height_trm_height_assn_sumC (Inl ba)")
  defer
  apply (simp add: eqvt_at_def height_trm_def)
  apply (simp add: eqvt_at_def height_trm_def)
  apply (simp add: eqvt_at_def height_assn_def)
  apply (simp add: eqvt_at_def height_assn_def)
  defer
  apply (subgoal_tac "height_assn as = height_assn asa")
  apply (subgoal_tac "height_trm b = height_trm ba")
  apply simp
  apply (erule_tac c="()" in Abs_lst_fcb2)
  apply (simp_all add: pure_fresh fresh_star_def)[3]
  apply (simp_all add: eqvt_at_def)[2]
  apply assumption
  apply (erule_tac Abs_lst_fcb)
  apply (simp_all add: pure_fresh fresh_star_def)[2]
  apply (drule what_we_would_like)
  apply (drule_tac x="p" in spec)
  apply simp
  apply (simp add: eqvt_at_def)
  oops

end



