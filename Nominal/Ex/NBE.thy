theory Lambda
imports 
  "../Nominal2"
begin


atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_datatype sem =
  L e::"env" x::"name" l::"lam" binds x "bn e" in l
| N "neu"
and neu = 
  V "name"
| A "neu" "sem"
and env =
  ENil
| ECons "env" "name" "sem"
binder
  bn
where
  "bn ENil = []"
| "bn (ECons env x v) = (atom x) # (bn env)"

thm sem_neu_env.supp

lemma [simp]:
  shows "finite (fv_bn env)"
apply(induct env rule: sem_neu_env.inducts(3))
apply(rule TrueI)+
apply(auto simp add: sem_neu_env.supp finite_supp)
done

lemma test1:
  shows "supp p \<sharp>* (fv_bn env) \<Longrightarrow> (p \<bullet> env) = permute_bn p env"
apply(induct env rule: sem_neu_env.inducts(3))
apply(rule TrueI)+
apply(auto simp add: sem_neu_env.perm_bn_simps sem_neu_env.supp)
apply(drule meta_mp)
apply(drule fresh_star_supp_conv)
apply(subst (asm) supp_finite_atom_set)
apply(simp add: finite_supp)
apply(simp add: fresh_star_Un)
apply(rule fresh_star_supp_conv)
apply(subst supp_finite_atom_set)
apply(simp)
apply(simp)
apply(simp)
apply(rule perm_supp_eq)
apply(drule fresh_star_supp_conv)
apply(subst (asm) supp_finite_atom_set)
apply(simp add: finite_supp)
apply(simp add: fresh_star_Un)
apply(rule fresh_star_supp_conv)
apply(simp)
done

thm alpha_sem_raw_alpha_neu_raw_alpha_env_raw_alpha_bn_raw.inducts(4)[no_vars]

lemma alpha_bn_inducts_raw[consumes 1]:
  "\<lbrakk>alpha_bn_raw x7 x8;
  P4 ENil_raw ENil_raw;
 \<And>env_raw env_rawa sem_raw sem_rawa name namea.
    \<lbrakk>alpha_bn_raw env_raw env_rawa; P4 env_raw env_rawa; alpha_sem_raw sem_raw sem_rawa\<rbrakk>
    \<Longrightarrow> P4 (ECons_raw env_raw name sem_raw) (ECons_raw env_rawa namea sem_rawa)\<rbrakk>
\<Longrightarrow> P4 x7 x8"
apply(induct rule: alpha_sem_raw_alpha_neu_raw_alpha_env_raw_alpha_bn_raw.inducts(4))
apply(rule TrueI)+
apply(auto)
done

lemmas alpha_bn_inducts[consumes 1] = alpha_bn_inducts_raw[quot_lifted]

lemma test2:
  shows "alpha_bn env1 env2 \<Longrightarrow> p \<bullet> (bn env1) = q \<bullet> (bn env2) \<Longrightarrow> permute_bn p env1 = permute_bn q env2"
apply(induct rule: alpha_bn_inducts)
apply(auto simp add: sem_neu_env.perm_bn_simps sem_neu_env.bn_defs)
apply(simp add: atom_eqvt)
done

lemma fresh_star_Union:
  assumes "as \<subseteq> bs" "bs \<sharp>* x"
  shows "as \<sharp>* x"
using assms by (auto simp add: fresh_star_def)
  

nominal_function  (invariant "\<lambda>x y. case x of Inl (x1, y1) \<Rightarrow> 
  supp y \<subseteq> (supp y1 - set (bn x1)) \<union> (fv_bn x1) | Inr (x2, y2) \<Rightarrow> supp y \<subseteq> supp x2 \<union> supp y2")
  evals :: "env \<Rightarrow> lam \<Rightarrow> sem" and
  evals_aux :: "sem \<Rightarrow> sem \<Rightarrow> sem"
where
  "evals ENil (Var x) = N (V x)"
| "evals (ECons tail y v) (Var x) = (if x = y then v else evals tail (Var x))" 
| "atom x \<sharp> env \<Longrightarrow> evals env (Lam [x]. t) = L env x t"
| "evals env (App t1 t2) = evals_aux (evals env t1) (evals env t2)"
| "set (atom x # bn env) \<sharp>* (fv_bn env, t') \<Longrightarrow> evals_aux (L env x t) t' = evals (ECons env x t') t"
| "evals_aux (N n) t' = N (A n t')"
apply(simp add: eqvt_def  evals_evals_aux_graph_def)
apply(perm_simp)
apply(simp)
apply(erule evals_evals_aux_graph.induct)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
apply(rule conjI)
apply(rule impI)
apply(blast)
apply(rule impI)
apply(simp add: supp_at_base)
apply(blast)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
apply(blast)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
apply(blast)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
apply(blast)
apply(simp add: sem_neu_env.supp lam.supp sem_neu_env.bn_defs)
--"completeness"
apply(case_tac x)
apply(simp)
apply(case_tac a)
apply(simp)
apply(case_tac aa rule: sem_neu_env.exhaust(3))
apply(simp add: sem_neu_env.fresh)
apply(case_tac b rule: lam.exhaust)
apply(metis)+
apply(case_tac aa rule: sem_neu_env.exhaust(3))
apply(rule_tac y="b" and c="env" in lam.strong_exhaust)
apply(metis)+
apply(simp add: fresh_star_def)
apply(simp)
apply(rule_tac y="b" and c="ECons env name sem" in lam.strong_exhaust)
apply(metis)+
apply(simp add: fresh_star_def)
apply(simp)
apply(case_tac b)
apply(simp)
apply(rule_tac y="a" and c="(a, ba)" in sem_neu_env.strong_exhaust(1))
apply(simp)
apply(rotate_tac 4)
apply(drule_tac x="name" in meta_spec)
apply(drule_tac x="env" in meta_spec)
apply(drule_tac x="ba" in meta_spec)
apply(drule_tac x="lam" in meta_spec)
apply(simp add:  sem_neu_env.alpha_refl)
apply(rotate_tac 9)
apply(drule_tac meta_mp)
apply(simp (no_asm_use) add: fresh_star_def sem_neu_env.fresh fresh_Pair)
apply(simp)
apply(subst fresh_finite_atom_set)
defer
apply(simp)
apply(subst fresh_finite_atom_set)
defer
apply(simp)
apply(metis)+
--"compatibility"
apply(all_trivials)
apply(simp)
apply(simp)
defer
apply(simp)
apply(simp)
apply (simp add: meta_eq_to_obj_eq[OF evals_def, symmetric, unfolded fun_eq_iff])
apply (subgoal_tac "eqvt_at (\<lambda>(a, b). evals a b) (ECons env x t'a, t)")
apply (subgoal_tac "eqvt_at (\<lambda>(a, b). evals a b) (ECons enva xa t'a, ta)")
apply (thin_tac "eqvt_at evals_evals_aux_sumC (Inl (ECons env x t'a, t))")
apply (thin_tac "eqvt_at evals_evals_aux_sumC (Inl (ECons enva xa t'a, ta))")
apply(erule conjE)+
defer
apply (simp_all add: eqvt_at_def evals_def)[3]
defer
defer
apply(simp add: sem_neu_env.alpha_refl)
apply(erule conjE)+
apply(erule_tac c="(env, enva)" in Abs_lst1_fcb2)
apply(simp add: Abs_fresh_iff)
apply(simp add: fresh_star_def)
apply(perm_simp)
apply(simp add: fresh_star_Pair perm_supp_eq)
apply(perm_simp)
apply(simp add: fresh_star_Pair perm_supp_eq)
apply(simp add: sem_neu_env.bn_defs sem_neu_env.supp)
using at_set_avoiding3
apply -
apply(drule_tac x="set (atom x # bn env)" in meta_spec)
apply(drule_tac x="(fv_bn env, fv_bn enva, env, enva, x, xa, t, ta, t'a)" in meta_spec)
apply(drule_tac x="[atom x # bn env]lst. t" in meta_spec)
apply(simp (no_asm_use) add: finite_supp Abs_fresh_star_iff)
apply(drule meta_mp)
apply(simp add: supp_Pair finite_supp supp_finite_atom_set)
apply(drule meta_mp)
apply(simp add: fresh_star_def)
apply(erule exE)
apply(erule conjE)+
apply(rule trans)
apply(rule sym)
apply(rule_tac p="p" in perm_supp_eq)
apply(simp)
apply(perm_simp)
apply(simp add: fresh_star_Un fresh_star_insert)
apply(rule conjI)
apply(simp (no_asm_use) add: fresh_star_def fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(rule conjI)
apply(simp (no_asm_use) add: fresh_star_def fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(rule conjI)
apply(simp (no_asm_use) add: fresh_star_def fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(simp (no_asm_use) add: fresh_star_def fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(simp add: eqvt_at_def perm_supp_eq)
apply(subst (3) perm_supp_eq)
apply(simp)
apply(simp add: fresh_star_def fresh_Pair)
apply(auto)[1]
apply(rotate_tac 6)
apply(drule sym)
apply(simp)
apply(rotate_tac 11)
apply(drule trans)
apply(rule sym)
apply(rule_tac p="p" in supp_perm_eq)
apply(assumption)
apply(rotate_tac 11)
apply(rule sym)
apply(simp add: atom_eqvt)
apply(simp (no_asm_use) add: Abs_eq_iff2 alphas)
apply(erule conjE | erule exE)+
apply(rule trans)
apply(rule sym)
apply(rule_tac p="pa" in perm_supp_eq)
apply(erule fresh_star_Union)
apply(simp (no_asm_use) add: fresh_star_insert fresh_star_Un)
apply(rule conjI)
apply(perm_simp)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(rule conjI)
apply(perm_simp)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_Pair)
apply(simp add: fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(rule conjI)
apply(perm_simp)
defer
apply(perm_simp)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_star_Pair)
apply(simp add: fresh_star_def fresh_def)
apply(simp add: supp_finite_atom_set)
apply(blast)
apply(simp)
apply(perm_simp)
apply(subst (3) perm_supp_eq)
apply(erule fresh_star_Union)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_star_def fresh_Pair)
apply(subgoal_tac "pa \<bullet> enva = p \<bullet> env")
apply(simp)
defer
apply(simp (no_asm_use) add: fresh_star_insert fresh_star_Un)
apply(simp (no_asm_use) add: fresh_star_def)
apply(rule ballI)
apply(subgoal_tac "a \<notin> supp ta - insert (atom xa) (set (bn enva)) \<union> (fv_bn enva \<union> supp t'a)")
apply(simp only: fresh_def)
apply(blast)
apply(simp (no_asm_use))
apply(rule conjI)
apply(blast)
apply(simp add: fresh_Pair)
apply(simp add: fresh_star_def fresh_def)
apply(simp add: supp_finite_atom_set)
apply(subst test1)
apply(erule fresh_star_Union)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_star_def fresh_Pair)
apply(subst test1)
apply(simp)
apply(simp add: fresh_star_insert fresh_star_Un)
apply(simp add: fresh_star_def fresh_Pair)
apply(rule sym)
apply(erule test2)
apply(perm_simp)
apply(simp)
done




text {* can probably not proved by a trivial size argument *}
termination (* apply(lexicographic_order) *)
sorry

lemma [eqvt]:
  shows "(p \<bullet> evals env t) = evals (p \<bullet> env) (p \<bullet> t)"
  and "(p \<bullet> evals_aux v s) = evals_aux (p \<bullet> v) (p \<bullet> s)"
sorry

(* fixme: should be a provided lemma *)
lemma fv_bn_finite:
  shows "finite (fv_bn env)"
apply(induct env rule: sem_neu_env.inducts(3))
apply(auto simp add: sem_neu_env.supp finite_supp)
done

lemma test:
  fixes env::"env"
  shows "supp (evals env t) \<subseteq> (supp t - set (bn env)) \<union> (fv_bn env)"
  and "supp (evals_aux s v) \<subseteq> (supp s) \<union> (supp v)"
apply(induct env t and s v rule: evals_evals_aux.induct)
apply(simp add: sem_neu_env.supp lam.supp supp_Nil sem_neu_env.bn_defs)
apply(simp add: sem_neu_env.supp lam.supp supp_Nil supp_Cons sem_neu_env.bn_defs)
apply(rule conjI)
apply(auto)[1]
apply(rule impI)
apply(simp)
apply(simp add: supp_at_base)
apply(blast)
apply(simp)
apply(subst sem_neu_env.supp)
apply(simp add: sem_neu_env.supp lam.supp)
apply(auto)[1]
apply(simp add: lam.supp sem_neu_env.supp)
apply(blast)
apply(simp add: sem_neu_env.supp sem_neu_env.bn_defs)
apply(blast)
apply(simp add: sem_neu_env.supp)
done


nominal_function
  reify :: "sem \<Rightarrow> lam" and
  reifyn :: "neu \<Rightarrow> lam"
where
  "atom x \<sharp> (env, y, t) \<Longrightarrow> reify (L env y t) = Lam [x]. (reify (evals (ECons env y (N (V x))) t))"
| "reify (N n) = reifyn n"
| "reifyn (V x) = Var x"
| "reifyn (A n d) = App (reifyn n) (reify d)"
apply(subgoal_tac "\<And>p x y. reify_reifyn_graph x y \<Longrightarrow> reify_reifyn_graph (p \<bullet> x) (p \<bullet> y)")
apply(simp add: eqvt_def)
apply(simp add: permute_fun_def)
apply(rule allI)
apply(rule ext)
apply(rule ext)
apply(rule iffI)
apply(drule_tac x="p" in meta_spec)
apply(drule_tac x="- p \<bullet> x" in meta_spec)
apply(drule_tac x="- p \<bullet> xa" in meta_spec)
apply(simp add: permute_bool_def)
apply(simp add: permute_bool_def)
apply(erule reify_reifyn_graph.induct)
apply(perm_simp)
apply(rule reify_reifyn_graph.intros)
apply(rule_tac p="-p" in permute_boolE)
apply(perm_simp add: permute_minus_cancel)
apply(simp)
apply(simp)
apply(perm_simp)
apply(rule reify_reifyn_graph.intros)
apply(simp)
apply(perm_simp)
apply(rule reify_reifyn_graph.intros)
apply(perm_simp)
apply(rule reify_reifyn_graph.intros)
apply(simp)
apply(simp)
apply(rule TrueI)
--"completeness"
apply(case_tac x)
apply(simp)
apply(case_tac a rule: sem_neu_env.exhaust(1))
apply(subgoal_tac "\<exists>x::name. atom x \<sharp> (env, name, lam)")
apply(metis)
apply(rule obtain_fresh)
apply(blast)
apply(blast)
apply(case_tac b rule: sem_neu_env.exhaust(2))
apply(simp)
apply(simp)
apply(metis)
--"compatibility"
apply(all_trivials)
defer
apply(simp)
apply(simp)
apply(simp)
apply(erule conjE)
apply (simp add: meta_eq_to_obj_eq[OF reify_def, symmetric, unfolded fun_eq_iff])
apply (subgoal_tac "eqvt_at (\<lambda>t. reify t) (evals (ECons env y (N (V x))) t)")
apply (subgoal_tac "eqvt_at (\<lambda>t. reify t) (evals (ECons enva ya (N (V xa))) ta)")
apply (thin_tac "eqvt_at reify_reifyn_sumC (Inl (evals (ECons env y (N (V x))) t))")
apply (thin_tac "eqvt_at reify_reifyn_sumC (Inl (evals (ECons enva ya (N (V xa))) ta))")
defer
apply (simp_all add: eqvt_at_def reify_def)[2]
apply(subgoal_tac "\<exists>c::name. atom c \<sharp> (x, xa, env, enva, y, ya, t, ta)")
prefer 2
apply(rule obtain_fresh)
apply(blast)
apply(erule exE)
apply(rule trans)
apply(rule sym)
apply(rule_tac a="x" and b="c" in flip_fresh_fresh)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff fresh_Pair)
apply(auto)[1]
apply(rule fresh_eqvt_at)
back
apply(assumption)
apply(simp add: finite_supp)
apply(rule_tac S="supp (env, y, x, t)" in supports_fresh)
apply(simp add: supports_def fresh_def[symmetric])
apply(perm_simp)
apply(simp add: swap_fresh_fresh fresh_Pair)
apply(simp add: finite_supp)
apply(simp add: fresh_def[symmetric])
apply(simp add: eqvt_at_def)
apply(simp add: eqvt_at_def[symmetric])
apply(perm_simp)
apply(simp add: flip_fresh_fresh)
apply(rule sym)
apply(rule trans)
apply(rule sym)
apply(rule_tac a="xa" and b="c" in flip_fresh_fresh)
apply(simp add: Abs_fresh_iff)
apply(simp add: Abs_fresh_iff fresh_Pair)
apply(auto)[1]
apply(rule fresh_eqvt_at)
back
apply(assumption)
apply(simp add: finite_supp)
apply(rule_tac S="supp (enva, ya, xa, ta)" in supports_fresh)
apply(simp add: supports_def fresh_def[symmetric])
apply(perm_simp)
apply(simp add: swap_fresh_fresh fresh_Pair)
apply(simp add: finite_supp)
apply(simp add: fresh_def[symmetric])
apply(simp add: eqvt_at_def)
apply(simp add: eqvt_at_def[symmetric])
apply(perm_simp)
apply(simp add: flip_fresh_fresh)
apply(simp (no_asm) add: Abs1_eq_iff)
(* HERE *)
thm at_set_avoiding3
using at_set_avoiding3
apply -
apply(drule_tac x="set (atom y # bn env)" in meta_spec)
apply(drule_tac x="(env, enva)" in meta_spec)
apply(drule_tac x="[atom y # bn env]lst. t" in meta_spec)
apply(simp (no_asm_use) add: finite_supp)
apply(drule meta_mp)
apply(rule Abs_fresh_star)
apply(auto)[1]
apply(erule exE)
apply(erule conjE)+
apply(drule_tac q="(x \<leftrightarrow> c)" in eqvt_at_perm)
apply(perm_simp)
apply(simp add: flip_fresh_fresh fresh_Pair)
apply(drule_tac q="(xa \<leftrightarrow> c)" in eqvt_at_perm)
apply(perm_simp)
apply(simp add: flip_fresh_fresh fresh_Pair)
apply(drule sym)
(* HERE *)
apply(rotate_tac 9)
apply(drule sym)
apply(rotate_tac 9)
apply(drule trans)
apply(rule sym)
apply(rule_tac p="p" in supp_perm_eq)
apply(assumption)
apply(simp)
apply(perm_simp)
apply(simp (no_asm_use) add: Abs_eq_iff2 alphas)
apply(erule conjE | erule exE)+
apply(clarify)
apply(rule trans)
apply(rule sym)
apply(rule_tac p="pa" in perm_supp_eq)
defer
apply(rule sym)
apply(rule trans)
apply(rule sym)
apply(rule_tac p="p" in perm_supp_eq)
defer
apply(simp add: atom_eqvt)
apply(drule_tac q="(x \<leftrightarrow> c)" in eqvt_at_perm)
apply(perm_simp)
apply(simp add: flip_fresh_fresh fresh_Pair)

apply(rule sym)
apply(erule_tac Abs_lst1_fcb2')
apply(rule fresh_eqvt_at)
back
apply(drule_tac q="(c \<leftrightarrow> x)" in eqvt_at_perm)
apply(perm_simp)
apply(simp add: flip_fresh_fresh)
apply(simp add: finite_supp)
apply(rule supports_fresh)
apply(rule_tac S="supp (enva, ya, xa, ta)" in supports_fresh)
apply(simp add: supports_def fresh_def[symmetric])
apply(perm_simp)
apply(simp add: swap_fresh_fresh fresh_Pair)
apply(simp add: finite_supp)
apply(simp add: fresh_def[symmetric])
apply(simp add: eqvt_at_def)
apply(simp add: eqvt_at_def[symmetric])
apply(perm_simp)
apply(rule fresh_eqvt_at)
back
apply(drule_tac q="(c \<leftrightarrow> x)" in eqvt_at_perm)
apply(perm_simp)
apply(simp add: flip_fresh_fresh)
apply(assumption)
apply(simp add: finite_supp)
sorry

termination sorry

definition
  eval :: "lam \<Rightarrow> sem"
where
  "eval t = evals ENil t"

definition
  normalize :: "lam \<Rightarrow> lam"
where
  "normalize t = reify (eval t)"

end
