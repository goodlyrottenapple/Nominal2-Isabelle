theory Lambda
imports "../Nominal2" 
begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

lemma fresh_fun_eqvt_app3:
  assumes a: "eqvt f"
  and b: "a \<sharp> x" "a \<sharp> y" "a \<sharp> z"
  shows "a \<sharp> f x y z"
  using fresh_fun_eqvt_app[OF a b(1)] a b
  by (metis fresh_fun_app)

lemma fresh_fun_eqvt_app4:
  assumes a: "eqvt f"
  and b: "a \<sharp> x" "a \<sharp> y" "a \<sharp> z" "a \<sharp> w"
  shows "a \<sharp> f x y z w"
  using fresh_fun_eqvt_app[OF a b(1)] a b
  by (metis fresh_fun_app)

lemma the_default_pty:
  assumes f_def: "f == (\<lambda>x::'a. THE_default d (G x))"
  and unique: "\<exists>!y. G x y"
  and pty: "\<And>x y. G x y \<Longrightarrow> P x y"
  shows "P x (f x)"
  apply(subst f_def)
  apply (rule ex1E[OF unique])
  apply (subst THE_default1_equality[OF unique])
  apply assumption
  apply (rule pty)
  apply assumption
  done

locale test =
  fixes f1::"name \<Rightarrow> name list \<Rightarrow> ('a::pt)"
    and f2::"lam \<Rightarrow> lam \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> name list \<Rightarrow> ('a::pt)"
    and f3::"name \<Rightarrow> lam \<Rightarrow> 'a \<Rightarrow> name list \<Rightarrow> ('a::pt)"
  assumes fs: "finite (supp (f1, f2, f3))"
    and eq: "eqvt f1" "eqvt f2" "eqvt f3"
    and fcb1: "\<And>l n. atom ` set l \<sharp>* f1 n l"
    and fcb2: "\<And>l t1 t2 r1 r2. atom ` set l \<sharp>* (r1, r2) \<Longrightarrow> atom ` set l \<sharp>* f2 t1 t2 r1 r2 l"
    and fcb3: "\<And>t l r. atom ` set (x # l) \<sharp>* r \<Longrightarrow> atom ` set (x # l) \<sharp>* f3 x t r l"
begin

nominal_function (invariant "\<lambda>(x, l) y. atom ` set l \<sharp>* y")
  f
where
  "f (Var x) l = f1 x l"
| "f (App t1 t2) l = f2 t1 t2 (f t1 l) (f t2 l) l"
| "atom x \<sharp> l \<Longrightarrow> (f (Lam [x].t) l) = f3 x t (f t (x # l)) l"
  apply (simp add: eqvt_def f_graph_def)
  apply (rule, perm_simp)
  apply (simp only: eq[unfolded eqvt_def])
  apply (erule f_graph.induct)
  apply (simp add: fcb1)
  apply (simp add: fcb2 fresh_star_Pair)
  apply simp
  apply (subgoal_tac "atom ` set (xa # l) \<sharp>* f3 xa t (f_sum (t, xa # l)) l")
  apply (simp add: fresh_star_def)
  apply (rule fcb3)
  apply (simp add: fresh_star_def fresh_def)
  apply simp_all
  apply(case_tac x)
  apply(rule_tac y="a" and c="b" in lam.strong_exhaust)
  apply(auto simp add: fresh_star_def)
  apply(erule Abs_lst1_fcb)
  apply (subgoal_tac "atom ` set (x # la) \<sharp>* f3 x t (f_sumC (t, x # la)) la")
  apply (simp add: fresh_star_def)
  apply (rule fcb3)
  apply (simp add: fresh_star_def)
  apply (rule fresh_fun_eqvt_app4[OF eq(3)])
  apply (simp add: fresh_at_base)
  apply assumption
  apply (erule fresh_eqvt_at)
  apply (simp add: finite_supp)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base)
  apply assumption
  apply (subgoal_tac "\<And>p y r l. p \<bullet> (f3 x y r l) = f3 (p \<bullet> x) (p \<bullet> y) (p \<bullet> r) (p \<bullet> l)")
  apply (subgoal_tac "(atom x \<rightleftharpoons> atom xa) \<bullet> la = la")
  apply (simp add: eqvt_at_def)
  apply (simp add: swap_fresh_fresh)
  apply (simp add: permute_fun_app_eq eq[unfolded eqvt_def])
  apply simp
  done

termination
  by (relation "measure (\<lambda>(x,_). size x)") (auto simp add: lam.size)

end

section {* Locally Nameless Terms *}

nominal_datatype ln = 
  LNBnd nat
| LNVar name
| LNApp ln ln
| LNLam ln

fun
  lookup :: "name list \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> ln" 
where
  "lookup [] n x = LNVar x"
| "lookup (y # ys) n x = (if x = y then LNBnd n else (lookup ys (n + 1) x))"

lemma lookup_eqvt[eqvt]:
  shows "(p \<bullet> lookup xs n x) = lookup (p \<bullet> xs) (p \<bullet> n) (p \<bullet> x)"
  by (induct xs arbitrary: n) (simp_all add: permute_pure)

lemma fresh_at_list: "atom x \<sharp> xs \<longleftrightarrow> x \<notin> set xs"
  unfolding fresh_def supp_set[symmetric]
  apply (induct xs)
  apply (simp add: supp_set_empty)
  apply simp
  apply auto
  apply (simp_all add: insert_absorb UnI2 finite_set supp_of_finite_insert supp_at_base)
  done

interpretation trans: test
  "%x l. lookup l 0 x"
  "%t1 t2 r1 r2 l. LNApp r1 r2"
  "%n t r l. LNLam r"
  apply default
  apply (auto simp add: pure_fresh supp_Pair)
  apply (simp_all add: fresh_def supp_def permute_fun_def permute_pure lookup_eqvt)[3]
  apply (simp_all add: eqvt_def permute_fun_def permute_pure lookup_eqvt)
  apply (simp add: fresh_star_def)
  apply (rule_tac x="0 :: nat" in spec)
  apply (induct_tac l)
  apply (simp add: ln.fresh pure_fresh)
  apply (auto simp add: ln.fresh pure_fresh)[1]
  apply (case_tac "a \<in> set list")
  apply simp
  apply (rule_tac f="lookup" in fresh_fun_eqvt_app3)
  unfolding eqvt_def
  apply rule
  using eqvts_raw(35)
  apply auto[1]
  apply (simp add: fresh_at_list)
  apply (simp add: pure_fresh)
  apply (simp add: fresh_at_base)
  apply (simp add: fresh_star_Pair fresh_star_def ln.fresh)
  apply (simp add: fresh_star_def ln.fresh)
  done

thm trans.f.simps

lemma lam_strong_exhaust2:
  "\<lbrakk>\<And>name. y = Var name \<Longrightarrow> P; 
    \<And>lam1 lam2. y = App lam1 lam2 \<Longrightarrow> P;
    \<And>name lam. \<lbrakk>{atom name} \<sharp>* c; y = Lam [name]. lam\<rbrakk> \<Longrightarrow> P;
    finite (supp c)\<rbrakk>
    \<Longrightarrow> P"
sorry

nominal_function
  g
where
  "(~finite (supp (g1, g2, g3))) \<Longrightarrow> g g1 g2 g3 t = t"
| "finite (supp (g1, g2, g3)) \<Longrightarrow> g g1 g2 g3 (Var x) = g1 x"
| "finite (supp (g1, g2, g3)) \<Longrightarrow> g g1 g2 g3 (App t1 t2) = g2 t1 t2 (g g1 g2 g3 t1) (g g1 g2 g3 t2)"
| "finite (supp (g1, g2, g3)) \<Longrightarrow> atom x \<sharp> (g1,g2,g3) \<Longrightarrow> (g g1 g2 g3 (Lam [x].t)) = g3 x t (g g1 g2 g3 t)"
  apply (simp add: eqvt_def g_graph_def)
  apply (rule, perm_simp, rule)
  apply simp_all
  apply (case_tac x)
  apply (case_tac "finite (supp (a, b, c))")
  prefer 2
  apply simp
  apply(rule_tac y="d" and c="(a,b,c)" in lam_strong_exhaust2)
  apply auto
  apply blast
  apply (simp add: Abs1_eq_iff fresh_star_def)
  sorry

termination
  by (relation "measure (\<lambda>(_,_,_,t). size t)") (simp_all add: lam.size)

end
