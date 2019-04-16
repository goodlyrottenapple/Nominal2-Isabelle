theory Let
imports "../Nominal2"
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Let as::"assn" t::"trm"   binds "bn as" in as t
and assn =
  ANil
| ACons "name" "trm" "assn"
binder
  bn
where
  "bn ANil = []"
| "bn (ACons x t as) = (atom x) # (bn as)"

nominal_function substrec where
  "substrec fa fl fd y z (Var x) = (if (y = x) then z else (Var x))"
| "substrec fa fl fd y z (App l r) = fa l r"
| "(set (bn as) \<sharp>* (Let as t, y, z) \<and> (\<forall>bs s. set (bn bs) \<sharp>* (Let bs s, y, z) \<longrightarrow> Let as t = Let bs s \<longrightarrow> fl as t = fl bs s)) \<Longrightarrow>
   substrec fa fl fd y z (Let as t) = fl as t"
| "(set (bn as) \<sharp>* (Let as t, y, z) \<and> \<not>(\<forall>bs s. set (bn bs) \<sharp>* (Let bs s, y, z) \<longrightarrow> Let as t = Let bs s \<longrightarrow> fl as t = fl bs s)) \<Longrightarrow>
   substrec fa fl fd y z (Let as t) = fd"
  unfolding eqvt_def substrec_graph_def
  apply (rule, perm_simp, rule, rule)
  apply (case_tac x)
  apply (rule_tac y="f" and c="(f, d, e)" in trm_assn.strong_exhaust(1))
  apply metis
  apply metis
  apply (thin_tac "\<And>fa fl fd y z xa. x = (fa, fl, fd, y, z, Var xa) \<Longrightarrow> P")
  apply (thin_tac "\<And>fa fl fd y z l r. x = (fa, fl, fd, y, z, App l r) \<Longrightarrow> P")
  apply (drule_tac x="assn" in meta_spec)+
  apply (drule_tac x="trm" in meta_spec)+
  apply (drule_tac x="d" in meta_spec)+
  apply (drule_tac x="e" in meta_spec)+
  apply (drule_tac x="b" in meta_spec)+
  apply (drule_tac x="a" in meta_spec)+
  apply (drule_tac x="c" in meta_spec)+
  apply (case_tac "(\<forall>bs s.
             set (bn bs) \<sharp>* (Let bs s, d, e) \<longrightarrow>
             Let.Let assn trm = Let.Let bs s \<longrightarrow> b assn trm = b bs s)")
  apply simp
  apply (thin_tac "set (bn assn) \<sharp>* (Let assn trm, d, e) \<and>
         (\<forall>bs s.
             set (bn bs) \<sharp>* (Let bs s, d, e) \<longrightarrow>
             Let.Let assn trm = Let.Let bs s \<longrightarrow> b assn trm = b bs s) \<Longrightarrow>
         x = (a, b, c, d, e, Let.Let assn trm) \<Longrightarrow> P")
  apply simp
  apply simp_all
  apply clarify
  apply metis
  done
nominal_termination (eqvt) by lexicographic_order

nominal_function substarec :: "(name \<Rightarrow> trm \<Rightarrow> assn \<Rightarrow> assn) \<Rightarrow> assn \<Rightarrow> assn" where
  "substarec fac ANil = ANil"
| "substarec fac (ACons x t as) = fac x t as"
  unfolding eqvt_def substarec_graph_def
  apply (rule, perm_simp, rule, rule)
  apply (case_tac x)
  apply (rule_tac y="b" in trm_assn.exhaust(2))
  apply auto
  done
nominal_termination (eqvt) by lexicographic_order

lemma [fundef_cong]:
 "(\<And>t1 t2. t = App t1 t2 \<Longrightarrow> fa t1 t2 = fa' t1 t2) \<Longrightarrow>
  (\<And>as s. t = Let as s \<Longrightarrow> fl as s = fl' as s) \<Longrightarrow>
  substrec fa fl fd y z t = substrec fa' fl' fd y z t"
  apply (rule_tac y="t" and c="(t, y, z)" in trm_assn.strong_exhaust(1))
  apply auto
  apply (case_tac "(\<forall>bs s. set (bn bs) \<sharp>* (Let bs s, y, z) \<longrightarrow> Let assn trm = Let bs s \<longrightarrow> fl assn trm = fl bs s)")
  apply (subst substrec.simps(3)) apply simp
  apply (subst substrec.simps(3)) apply simp
  apply metis
  apply (subst substrec.simps(4)) apply simp
  apply (subst substrec.simps(4)) apply simp_all
  done

lemma [fundef_cong]:
 "(\<And>x s as. t = ACons x s as \<Longrightarrow> fac x s as = fac' x s as) \<Longrightarrow>
  substarec fac t = substarec fac' t"
  by (rule_tac y="t" in trm_assn.exhaust(2)) simp_all

function
    subst  :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
and substa :: "name \<Rightarrow> trm \<Rightarrow> assn \<Rightarrow> assn"
where
  [simp del]: "subst y z t = substrec
     (\<lambda>l r. App (subst y z l) (subst y z r))
     (\<lambda>as t. Let (substa y z as) (subst y z t))
     (Let (ACons y (Var y) ANil) (Var y)) y z t"
| [simp del]: "substa y z t = substarec
     (\<lambda>x t as. ACons x (subst y z t) (substa y z as)) t"
  by pat_completeness auto

termination by lexicographic_order

lemma testl:
  assumes a: "\<exists>y. f x = Inl y"
  shows "(p \<bullet> (Sum_Type.Projl (f x))) = Sum_Type.Projl ((p \<bullet> f) (p \<bullet> x))"
using a
apply clarify
apply(frule_tac p="p" in permute_boolI)
apply(simp (no_asm_use) only: eqvts)
apply(subst (asm) permute_fun_app_eq)
back
apply(simp)
done

lemma testr:
  assumes a: "\<exists>y. f x = Inr y"
  shows "(p \<bullet> (Sum_Type.Projr (f x))) = Sum_Type.Projr ((p \<bullet> f) (p \<bullet> x))"
using a
apply clarify
apply(frule_tac p="p" in permute_boolI)
apply(simp (no_asm_use) only: eqvts)
apply(subst (asm) permute_fun_app_eq)
back
apply(simp)
done

lemma permute_move: "p \<bullet> x = y \<longleftrightarrow> x = -p \<bullet> y"
  by (metis eqvt_bound unpermute_def)

lemma "subst_substa_graph x t \<Longrightarrow> subst_substa_graph (p \<bullet> x) (p \<bullet> t)"
proof (induct arbitrary: p rule: subst_substa_graph.induct)
fix f y z t p
assume a: "\<And>t1 t2 p. t = App t1 t2 \<Longrightarrow> subst_substa_graph (p \<bullet> Inl (y, z, t1)) (p \<bullet> f (Inl (y, z, t1)))"
   and b: "\<And>t1 t2 p. t = App t1 t2 \<Longrightarrow> subst_substa_graph (p \<bullet> Inl (y, z, t2)) (p \<bullet> f (Inl (y, z, t2)))"
   and c: "\<And>as s p. t = Let.Let as s \<Longrightarrow> subst_substa_graph (p \<bullet> Inr (y, z, as)) (p \<bullet> f (Inr (y, z, as)))"
   and d: "\<And>as s p. t = Let.Let as s \<Longrightarrow> subst_substa_graph (p \<bullet> Inl (y, z, s)) (p \<bullet> f (Inl (y, z, s)))"
   then show "subst_substa_graph (p \<bullet> Inl (y, z, t))
           (p \<bullet> Inl (substrec
                      (\<lambda>l r. App (Sum_Type.Projl (f (Inl (y, z, l))))
                              (Sum_Type.Projl (f (Inl (y, z, r)))))
                      (\<lambda>as t. Let.Let (Sum_Type.Projr (f (Inr (y, z, as))))
                               (Sum_Type.Projl (f (Inl (y, z, t)))))
                      (Let.Let (ACons y (Var y) ANil) (Var y)) y z t))"
     proof (rule_tac y="t" and c="(t, y, z)" in trm_assn.strong_exhaust(1))
       fix name
       assume "t = Var name"
       then show ?thesis
         apply (simp add: eqvts split del: if_splits)
         apply (simp only:  trm_assn.perm_simps)
         apply (rule subst_substa_graph.intros(1)[of "Var (p \<bullet> name)" "p \<bullet> y" "p \<bullet> z", simplified])
         by simp_all
     next
       fix trm1 trm2
       assume e: "t = App trm1 trm2"
       then show ?thesis
         apply (simp add: eqvts)
         apply (subst testl) back
         apply (rule subst_substa_graph.cases[OF a[OF e, of 0, simplified]])
         apply metis apply simp
         apply (subst testl) back
         apply (rule subst_substa_graph.cases[OF b[OF e, of 0, simplified]])
         apply metis apply (simp add: eqvts)
         apply (simp only: Inl_eqvt) apply simp
         apply (rule subst_substa_graph.intros(1)[of "App (p \<bullet> trm1) (p \<bullet> trm2)" "p \<bullet> y" "p \<bullet> z", simplified])
         apply simp_all apply clarify
         using a[OF e, simplified Inl_eqvt, simplified]
         apply (metis (lifting) Inl_eqvt permute_fun_app_eq permute_prod.simps)
         apply clarify
         using b[OF e, simplified Inl_eqvt, simplified]
         by (metis (lifting) Inl_eqvt permute_fun_app_eq permute_prod.simps)
     next
       fix assn trm
       assume e: "t = Let.Let assn trm" and f: "set (bn assn) \<sharp>* (t, y, z)"
       then show ?thesis
         apply (simp add: eqvts)
         apply (simp only: permute_fun_def)
         apply (simp only: eqvts permute_minus_cancel)
         apply (case_tac "(\<forall>bs s. set (bn bs) \<sharp>* (Let.Let bs s, p \<bullet> y, p \<bullet> z) \<longrightarrow>
                 Let.Let (p \<bullet> assn) (p \<bullet> trm) = Let.Let bs s \<longrightarrow>
                 Let.Let (p \<bullet> Sum_Type.Projr (f (Inr (y, z, - p \<bullet> p \<bullet> assn))))
                  (p \<bullet> Sum_Type.Projl (f (Inl (y, z, - p \<bullet> p \<bullet> trm)))) =
                 Let.Let (p \<bullet> Sum_Type.Projr (f (Inr (y, z, - p \<bullet> bs))))
                  (p \<bullet> Sum_Type.Projl (f (Inl (y, z, - p \<bullet> s)))))")
         prefer 2
         apply (subst substrec.simps(4))
         apply rule
         apply (simp add: fresh_star_Pair)
         apply (intro conjI)
         apply (metis fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4) trm_assn.perm_simps(3))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         apply assumption
         prefer 2
         apply (subst substrec.simps(3))
         apply rule
         apply (simp add: fresh_star_Pair)
         apply (intro conjI)
         apply (metis fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4) trm_assn.perm_simps(3))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         apply assumption
(*       The following subgoal is motivated by:
   thm subst_substa_graph.intros(1)[of "Let (p \<bullet> assn) (p \<bullet> trm)" "p \<bullet> y" "p \<bullet> z" "(p \<bullet> f)", simplified]*)
         apply (subgoal_tac "subst_substa_graph (Inl (p \<bullet> y, p \<bullet> z, Let.Let (p \<bullet> assn) (p \<bullet> trm)))
           (Inl (substrec
           (\<lambda>l r. App (Sum_Type.Projl ((p \<bullet> f) (Inl (p \<bullet> y, p \<bullet> z, l))))
                   (Sum_Type.Projl ((p \<bullet> f) (Inl (p \<bullet> y, p \<bullet> z, r)))))
           (\<lambda>as t. Let.Let (Sum_Type.Projr ((p \<bullet> f) (Inr (p \<bullet> y, p \<bullet> z, as))))
                    (Sum_Type.Projl ((p \<bullet> f) (Inl (p \<bullet> y, p \<bullet> z, t)))))
           (Let.Let (ACons (p \<bullet> y) (Var (p \<bullet> y)) ANil) (Var (p \<bullet> y))) (p \<bullet> y) (p \<bullet> z)
           (Let.Let (p \<bullet> assn) (p \<bullet> trm))))")
         apply (subst (asm) substrec.simps(3))
         apply rule
         apply (simp add: fresh_star_Pair)
         apply (intro conjI)
         apply (metis fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4) trm_assn.perm_simps(3))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         apply (metis (lifting) fresh_star_permute_iff set_eqvt trm_assn.fv_bn_eqvt(4))
         (* We don't have equivariance of Projl/Projr at the arbitrary 'bs' point *)
         defer
         apply (subst testr) back
         apply (rule subst_substa_graph.cases[OF c[OF e, of 0, simplified]])
         apply simp apply simp
         apply (subst testl) back
         apply (rule subst_substa_graph.cases[OF d[OF e, of 0, simplified]])
         apply simp apply simp apply simp
         apply (rule subst_substa_graph.intros(1)[of "Let (p \<bullet> assn) (p \<bullet> trm)" "p \<bullet> y" "p \<bullet> z" "(p \<bullet> f)", simplified])
         apply simp apply simp (* These two should follow by d for arbitrary 'as' point *)
         defer defer
         sorry
     qed
   next
     fix f y z t p
     show "subst_substa_graph (p \<bullet> Inr (y, z, t)) (p \<bullet> Inr (substarec (\<lambda>x t as. ACons
       x (Sum_Type.Projl (f (Inl (y, z, t)))) (Sum_Type.Projr (f (Inr (y, z, as))))) t))"
       sorry
   qed

(* Will follow from above and accp *)
lemma [eqvt]:
  "p \<bullet> (subst y z t) = subst (p \<bullet> y) (p \<bullet> z) (p \<bullet> t)"
  "p \<bullet> (substa y z t2) = substa (p \<bullet> y) (p \<bullet> z) (p \<bullet> t2)"
  sorry

lemma substa_simps[simp]:
  "substa y z ANil = ANil"
  "substa y z (ACons x t as) = ACons x (subst y z t) (substa y z as)"
  apply (subst substa.simps) apply (subst substarec.simps) apply rule
  apply (subst substa.simps) apply (subst substarec.simps) apply rule
  done

lemma bn_substa: "bn (substa y z t) = bn t"
  by (induct t rule: trm_assn.inducts(2)) (simp_all add: trm_assn.bn_defs)

lemma fresh_fun_eqvt_app3:
  assumes e: "eqvt f"
  shows "\<lbrakk>a \<sharp> x; a \<sharp> y; a \<sharp> z\<rbrakk> \<Longrightarrow> a \<sharp> f x y z"
  using fresh_fun_eqvt_app[OF e] fresh_fun_app by (metis (lifting, full_types))

lemma
  "subst y z (Var x) = (if (y = x) then z else (Var x))"
  "subst y z (App l r) = App (subst y z l) (subst y z r)"
  "set (bn as) \<sharp>* (Let as t, y, z) \<Longrightarrow> subst y z (Let as t) = Let (substa y z as) (subst y z t)"
  apply (subst subst.simps) apply (subst substrec.simps) apply rule
  apply (subst subst.simps) apply (subst substrec.simps) apply rule
  apply (subst subst.simps) apply (subst substrec.simps) apply auto
  apply (subst (asm) Abs_eq_iff2)
  apply clarify
  apply (simp add: alphas bn_substa)
  apply (rule_tac s="p \<bullet> ([bn as]lst. (substa y z as, subst y z t))" in trans)
  apply (rule sym)
  defer
  apply (simp add: eqvts)
  apply (subgoal_tac "supp p \<sharp>* y")
  apply (subgoal_tac "supp p \<sharp>* z")
  apply (simp add: perm_supp_eq)
  apply (simp add: fresh_Pair fresh_star_def)
  apply blast
  apply (simp add: fresh_Pair fresh_star_def)
  apply blast
  apply (rule perm_supp_eq)
  apply (simp add: fresh_star_Pair)
  apply (simp add: fresh_star_def Abs_fresh_iff)
  apply (auto)
  apply (simp add: bn_substa fresh_Pair)
  apply (rule)
  apply (rule fresh_fun_eqvt_app3[of substa])
  apply (simp add: eqvt_def eqvts_raw)
  apply (metis (lifting) Diff_partition Un_iff)
  apply (metis (lifting) Diff_partition Un_iff)
  apply (simp add: fresh_def trm_assn.supp)
  apply (metis (lifting) DiffI UnI1 supp_Pair)
  apply (rule fresh_fun_eqvt_app3[of subst])
  apply (simp add: eqvt_def eqvts_raw)
  apply (metis (lifting) Diff_partition Un_iff)
  apply (metis (lifting) Diff_partition Un_iff)
  apply (simp add: fresh_def trm_assn.supp)
  by (metis Diff_iff Un_iff supp_Pair)

end
