theory LetSimple1
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype trm =
  Var "name"
| App "trm" "trm"
| Let x::"name" "trm" t::"trm"   binds x in t

print_theorems

thm trm.fv_defs
thm trm.eq_iff 
thm trm.bn_defs
thm trm.bn_inducts
thm trm.perm_simps
thm trm.induct
thm trm.inducts
thm trm.distinct
thm trm.supp
thm trm.fresh
thm trm.exhaust
thm trm.strong_exhaust
thm trm.perm_bn_simps

nominal_function
    height_trm :: "trm \<Rightarrow> nat"
where
  "height_trm (Var x) = 1"
| "height_trm (App l r) = max (height_trm l) (height_trm r)"
| "height_trm (Let x t s) = max (height_trm t) (height_trm s)"
  apply (simp only: eqvt_def height_trm_graph_def)
  apply (rule, perm_simp, rule, rule TrueI)
  apply (case_tac x rule: trm.exhaust(1))
  apply (auto)[3]
  apply(simp_all)[5]
  apply (subgoal_tac "height_trm_sumC t = height_trm_sumC ta")
  apply (subgoal_tac "height_trm_sumC s = height_trm_sumC sa")
  apply simp
  apply(simp)
  apply(erule conjE)
  apply(erule_tac c="()" in Abs_lst1_fcb2)
  apply(simp_all add: fresh_star_def pure_fresh)[2]
  apply(simp_all add: eqvt_at_def)[2]
  apply(simp)
  done

termination
  by lexicographic_order


nominal_function (invariant "\<lambda>x (y::atom set). finite y")
  frees_set :: "trm \<Rightarrow> atom set"
where
  "frees_set (Var x) = {atom x}"
| "frees_set (App t1 t2) = frees_set t1 \<union> frees_set t2"
| "frees_set (Let x t s) = (frees_set s) - {atom x} \<union> (frees_set t)"
  apply(simp add: eqvt_def frees_set_graph_def)
  apply(rule, perm_simp, rule)
  apply(erule frees_set_graph.induct)
  apply(auto)[3]
  apply(rule_tac y="x" in trm.exhaust)
  apply(auto)[3]
  apply(simp_all)[5]
  apply(simp)
  apply(erule conjE)
  apply(subgoal_tac "frees_set_sumC s - {atom x} = frees_set_sumC sa - {atom xa}")
  apply(simp)
  apply(erule_tac c="()" in Abs_lst1_fcb2)
  apply(simp add: fresh_minus_atom_set)
  apply(simp add: fresh_star_def fresh_Unit)
  apply(simp add: Diff_eqvt eqvt_at_def, perm_simp, rule refl)
  apply(simp add: Diff_eqvt eqvt_at_def, perm_simp, rule refl)
  done

termination
  by lexicographic_order


nominal_function
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm"  ("_ [_ ::= _]" [90, 90, 90] 90)
where
  "(Var x)[y ::= s] = (if x = y then s else (Var x))"
| "(App t1 t2)[y ::= s] = App (t1[y ::= s]) (t2[y ::= s])"
| "atom x \<sharp> (y, s) \<Longrightarrow> (Let x t t')[y ::= s] = Let x (t[y ::= s]) (t'[y ::= s])"
  apply(simp add: eqvt_def subst_graph_def)
  apply (rule, perm_simp, rule)
  apply(rule TrueI)
  apply(auto)[1]
  apply(rule_tac y="a" and c="(aa, b)" in trm.strong_exhaust)
  apply(blast)+
  apply(simp_all add: fresh_star_def fresh_Pair_elim)[1]
  apply(blast)
  apply(simp_all)[5]
  apply(simp (no_asm_use))
  apply(simp)
  apply(erule conjE)+
  apply (erule_tac c="(ya,sa)" in Abs_lst1_fcb2)
  apply(simp add: Abs_fresh_iff)
  apply(simp add: fresh_star_def fresh_Pair)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
  apply(simp add: eqvt_at_def atom_eqvt fresh_star_Pair perm_supp_eq)
done

termination
  by lexicographic_order


end
