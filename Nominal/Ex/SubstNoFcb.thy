theory Lambda imports "../Nominal2" begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_function lam_rec ::
  "(name \<Rightarrow> 'a :: pt) \<Rightarrow> (lam \<Rightarrow> lam \<Rightarrow> 'a) \<Rightarrow> (name \<Rightarrow> lam \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b :: fs \<Rightarrow> lam \<Rightarrow> 'a"
where
  "lam_rec fv fa fl fd P (Var n) = fv n"
| "lam_rec fv fa fl fd P (App l r) = fa l r"
| "(atom x \<sharp> P \<and> (\<forall>y s. atom y \<sharp> P \<longrightarrow> Lam [x]. t = Lam [y]. s \<longrightarrow> fl x t = fl y s)) \<Longrightarrow>
     lam_rec fv fa fl fd P (Lam [x]. t) = fl x t"
| "(atom x \<sharp> P \<and> \<not>(\<forall>y s. atom y \<sharp> P \<longrightarrow> Lam [x]. t = Lam [y]. s \<longrightarrow> fl x t = fl y s)) \<Longrightarrow>
     lam_rec fv fa fl fd P (Lam [x]. t) = fd"
  apply (simp add: eqvt_def lam_rec_graph_def)
  apply (rule, perm_simp, rule, rule)
  apply (case_tac x)
  apply (rule_tac y="f" and c="e" in lam.strong_exhaust)
  apply metis
  apply metis
  unfolding fresh_star_def
  apply simp
  apply metis
  apply simp_all[2]
  apply (metis (no_types) Pair_inject lam.distinct)+
  apply simp
  apply (metis (no_types) Pair_inject lam.distinct)+
  done

nominal_termination (eqvt) by lexicographic_order

lemma lam_rec_cong[fundef_cong]:
  " (\<And>v. l = Var v \<Longrightarrow> fv v = fv' v) \<Longrightarrow>
    (\<And>t1 t2. l = App t1 t2 \<Longrightarrow> fa t1 t2 = fa' t1 t2) \<Longrightarrow>
    (\<And>n t. l = Lam [n]. t \<Longrightarrow> fl n t = fl' n t) \<Longrightarrow>
  lam_rec fv fa fl fd P l = lam_rec fv' fa' fl' fd P l"
  apply (rule_tac y="l" and c="P" in lam.strong_exhaust)
  apply auto
  apply (case_tac "(\<forall>y s. atom y \<sharp> P \<longrightarrow> Lam [name]. lam = Lam [y]. s \<longrightarrow> fl name lam = fl y s)")
  apply (subst lam_rec.simps) apply (simp add: fresh_star_def)
  apply (subst lam_rec.simps) apply (simp add: fresh_star_def)
  using Abs1_eq_iff lam.eq_iff apply metis
  apply (subst lam_rec.simps(4)) apply (simp add: fresh_star_def)
  apply (subst lam_rec.simps(4)) apply (simp add: fresh_star_def)
  using Abs1_eq_iff lam.eq_iff apply metis
  done

nominal_function substr where
[simp del]: "substr l y s = lam_rec
  (%x. if x = y then s else (Var x))
  (%t1 t2. App (substr t1 y s) (substr t2 y s))
  (%x t. Lam [x]. (substr t y s)) (Lam [y]. Var y) (y, s) l"
unfolding eqvt_def substr_graph_def
apply (rule, perm_simp, rule, rule)
by pat_completeness auto

nominal_termination (eqvt) by lexicographic_order

lemma fresh_fun_eqvt_app3:
  assumes e: "eqvt f"
  shows "\<lbrakk>a \<sharp> x; a \<sharp> y; a \<sharp> z\<rbrakk> \<Longrightarrow> a \<sharp> f x y z"
  using fresh_fun_eqvt_app[OF e] fresh_fun_app by (metis (lifting, full_types))

lemma substr_simps:
  "substr (Var x) y s = (if x = y then s else (Var x))"
  "substr (App t1 t2) y s = App (substr t1 y s) (substr t2 y s)"
  "atom x \<sharp> (y, s) \<Longrightarrow> substr (Lam [x]. t) y s = Lam [x]. (substr t y s)"
  apply (subst substr.simps) apply (simp only: lam_rec.simps)
  apply (subst substr.simps) apply (simp only: lam_rec.simps)
  apply (subst substr.simps) apply (subst lam_rec.simps)
  apply (auto simp add: Abs1_eq_iff substr.eqvt swap_fresh_fresh)
  apply (rule fresh_fun_eqvt_app3[of substr])
  apply (simp add: eqvt_def eqvts_raw)
  apply (simp_all add: fresh_Pair)
  done

end



