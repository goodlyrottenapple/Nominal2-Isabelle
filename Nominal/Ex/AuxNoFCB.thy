theory Lambda imports "../Nominal2" begin

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

nominal_function lookup where
  "lookup (n :: name) m [] \<longleftrightarrow> (n = m)"
| "lookup n m ((hn, hm) # t) \<longleftrightarrow>
     (n, m) = (hn, hm) \<or> (n \<noteq> hn \<and> m \<noteq> hm \<and> lookup n m t)"
  apply (simp add: eqvt_def lookup_graph_def)
  apply (rule, perm_simp, rule, rule)
  by pat_completeness auto

nominal_termination (eqvt) by lexicographic_order

nominal_function lam2_rec where
  "lam2_rec faa fll xs (Var n) (Var m) = lookup n m xs"
| "lam2_rec faa fll xs (Var n) (App l r) = False"
| "lam2_rec faa fll xs (Var n) (Lam [x]. t) = False"
| "lam2_rec faa fll xs (App l r) (Var n) = False"
| "lam2_rec faa fll xs (App l1 r1) (App l2 r2) = faa l1 r1 l2 r2"
| "lam2_rec faa fll xs (App l r) (Lam [x]. t) = False"
| "lam2_rec faa fll xs (Lam [x]. t) (Var n) = False"
| "lam2_rec faa fll xs (Lam [x]. t) (App l1 r1) = False"
| "(atom x \<sharp> (xs, Lam [y]. s) \<and> atom y \<sharp> (x, xs, Lam [x]. t) \<and>
     (\<forall>x' y' t' s'. atom x' \<sharp> (xs, Lam [y']. s') \<longrightarrow> atom y' \<sharp> (x', xs, Lam [x']. t') \<longrightarrow> Lam [x]. t = Lam [x']. t' \<longrightarrow> Lam [y]. s = Lam [y']. s'
        \<longrightarrow> fll x t y s = fll x' t' y' s')) \<Longrightarrow>
     lam2_rec faa fll xs (Lam [x]. t) (Lam [y]. s) = fll x t y s"
| "(atom x \<sharp> (xs, Lam [y]. s) \<and> atom y \<sharp> (x, xs, Lam [x]. t) \<and>
     \<not>(\<forall>x' y' t' s'. atom x' \<sharp> (xs, Lam [y']. s') \<longrightarrow> atom y' \<sharp> (x', xs, Lam [x']. t') \<longrightarrow> Lam [x]. t = Lam [x']. t' \<longrightarrow> Lam [y]. s = Lam [y']. s'
        \<longrightarrow> fll x t y s = fll x' t' y' s')) \<Longrightarrow>
     lam2_rec faa fll xs (Lam [x]. t) (Lam [y]. s) = False"
  apply (simp add: eqvt_def lam2_rec_graph_def)
  apply (rule, perm_simp, rule, rule)
  apply (case_tac x)
  apply (rule_tac y="d" and c="(c, e)" in lam.strong_exhaust)
  apply (rule_tac y="e" and c="(c, d)" in lam.strong_exhaust)
  apply simp_all[3]  apply (metis, metis, metis)
  apply (rule_tac y="e" and c="(c, d)" in lam.strong_exhaust)
  apply simp_all[3]  apply (metis, metis, metis)
  apply (rule_tac y="e" and c="(name, c, d)" in lam.strong_exhaust)
  apply simp_all[2]  apply (metis, metis)
  unfolding fresh_star_def
  apply (thin_tac "\<And>faa fll xs n m. x = (faa, fll, xs, Var n, Var m) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs n l r. x = (faa, fll, xs, Var n, App l r) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs n xa t. x = (faa, fll, xs, Var n, Lam [xa]. t) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs l1 r1 l2 r2. x = (faa, fll, xs, App l1 r1, App l2 r2) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs l r n. x = (faa, fll, xs, App l r, Var n) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs l r xa t. x = (faa, fll, xs, App l r, Lam [xa]. t) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs xa t n. x = (faa, fll, xs, Lam [xa]. t, Var n) \<Longrightarrow> P")
  apply (thin_tac "\<And>faa fll xs xa t l1 r1. x = (faa, fll, xs, Lam [xa]. t, App l1 r1) \<Longrightarrow> P")
  apply (drule_tac x="name" in meta_spec)+
  apply (drule_tac x="c" in meta_spec)+
  apply (drule_tac x="namea" in meta_spec)+
  apply (drule_tac x="lama" in meta_spec)
  apply (drule_tac x="lama" in meta_spec)
  apply (drule_tac x="lam" in meta_spec)+
  apply (drule_tac x="b" in meta_spec)+
  apply (drule_tac x="a" in meta_spec)+
  apply (case_tac "(\<forall>x' y' t' s'. atom x' \<sharp> (c, Lam [y']. s') \<longrightarrow>
             atom y' \<sharp> (x', c, Lam [x']. t') \<longrightarrow> Lam [name]. lam = Lam [x']. t' \<longrightarrow>
             Lam [namea]. lama = Lam [y']. s' \<longrightarrow> b name lam namea lama = b x' t' y' s')")
  apply clarify
  apply (simp)
  apply (simp only: fresh_Pair_elim)
  apply blast
  apply (simp_all)[53]
  apply clarify
  apply metis
  apply simp
  done

nominal_termination (eqvt) by lexicographic_order

lemma lam_rec2_cong[fundef_cong]:
  "(\<And>s1 s2 s3 s4. l = App s1 s2 \<Longrightarrow> l2 = App s3 s4  \<Longrightarrow> faa s1 s2 s3 s4 = faa' s1 s2 s3 s4) \<Longrightarrow>
   (\<And>n t n' t'. l = Lam [n]. t \<Longrightarrow> l2 = Lam [n']. t' \<Longrightarrow> fll n t n' t' = fll' n t n' t') \<Longrightarrow>
  lam2_rec faa fll xs l l2 = lam2_rec faa' fll' xs l l2"
  apply (rule_tac y="l" and c="(xs, l2)" in lam.strong_exhaust)
  apply (rule_tac y="l2" and c="(xs, l)" in lam.strong_exhaust) apply auto[3]
  apply (rule_tac y="l2" and c="(xs, l)" in lam.strong_exhaust) apply auto[3]
  apply (rule_tac y="l2" and c="(name, xs, l)" in lam.strong_exhaust)
  apply auto[2]
  apply clarify
  apply (case_tac "(\<forall>x' y' t' s'. atom x' \<sharp> (xs, Lam [y']. s') \<longrightarrow>
    atom y' \<sharp> (x', xs, Lam [x']. t') \<longrightarrow> Lam [name]. lam = Lam [x']. t' \<longrightarrow>
    Lam [namea]. lama = Lam [y']. s' \<longrightarrow> fll name lam namea lama = fll x' t' y' s')")
  unfolding fresh_star_def
  apply (subst lam2_rec.simps) apply simp
  apply (subst lam2_rec.simps) apply simp
  apply metis
  apply (subst lam2_rec.simps(10)) apply (simp add: fresh_star_def)
  apply (subst lam2_rec.simps(10)) apply (simp_all add: fresh_star_def)
  done

nominal_function aux :: "lam \<Rightarrow> lam \<Rightarrow> (name \<times> name) list \<Rightarrow> bool"
  where
[simp del]: "aux l r xs = lam2_rec
  (%t1 t2 t3 t4. (aux t1 t3 xs) \<and> (aux t2 t4 xs))
  (%x t y s. aux t s ((x, y) # xs)) xs l r"
  unfolding eqvt_def aux_graph_def
  apply (rule, perm_simp, rule, rule)
  by pat_completeness auto

nominal_termination (eqvt)
  by (relation "measure (\<lambda>(l, r, xs). size l + size r)") simp_all

lemma aux_simps[simp]:
  "aux (Var x) (Var y) xs = lookup x y xs"
  "aux (App t1 t2) (App s1 s2) xs = (aux t1 s1 xs \<and> aux t2 s2 xs)"
  "aux (Var x) (App t1 t2) xs = False"
  "aux (Var x) (Lam [y].t) xs = False"
  "aux (App t1 t2) (Var x) xs = False"
  "aux (App t1 t2) (Lam [x].t) xs = False"
  "aux (Lam [x].t) (Var y) xs = False"
  "aux (Lam [x].t) (App t1 t2) xs = False"
  "\<lbrakk>atom x \<sharp> (s, xs); atom y \<sharp> (x, t, xs)\<rbrakk> \<Longrightarrow> aux (Lam [x].t) (Lam [y].s) xs = aux t s ((x, y) # xs)"
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps, simp)
  apply (subst aux.simps)
  apply (subst lam2_rec.simps)
  apply (rule, simp add: lam.fresh)
  apply (rule, simp add: lam.fresh)
  apply (intro allI impI)
  apply (rule_tac x="(x, x', y, y', t, t', s, s', xs)" and ?'a="name" in obtain_fresh)
  apply (rule_tac x="(a, x, x', y, y', t, t', s, s', xs)" and ?'a="name" in obtain_fresh)
  apply (rule_tac s="aux ((atom x \<rightleftharpoons> atom a) \<bullet> t) s ((a, y) # xs)" in trans)
  apply (rule_tac s="(atom x \<rightleftharpoons> atom a) \<bullet> aux t s ((x, y) # xs)" in trans)
  apply (rule permute_pure[symmetric])
  apply (simp add: eqvts swap_fresh_fresh)
  apply (simp add: lam.fresh fresh_at_base fresh_Pair_elim)
  apply (rename_tac b)
  apply (rule_tac s="aux ((atom x \<rightleftharpoons> atom a) \<bullet> t) ((atom y \<rightleftharpoons> atom b) \<bullet> s) ((a, b) # xs)" in trans)
  apply (rule_tac s="(atom y \<rightleftharpoons> atom b) \<bullet> aux ((atom x \<rightleftharpoons> atom a) \<bullet> t) s ((a, y) # xs)" in trans)
  apply (rule permute_pure[symmetric])
  apply (simp add: eqvts swap_fresh_fresh)
  apply (simp add: lam.fresh fresh_at_base fresh_Pair_elim)
  apply (subst permute_eqvt)
  apply (simp add: eqvts swap_fresh_fresh)
  apply (rule sym)
  apply (rule_tac s="aux ((atom x' \<rightleftharpoons> atom a) \<bullet> t') s' ((a, y') # xs)" in trans)
  apply (rule_tac s="(atom x' \<rightleftharpoons> atom a) \<bullet> aux t' s' ((x', y') # xs)" in trans)
  apply (rule permute_pure[symmetric])
  apply (simp add: eqvts swap_fresh_fresh)
  apply (simp add: lam.fresh fresh_at_base fresh_Pair_elim swap_fresh_fresh)
  apply (rule_tac s="aux ((atom x' \<rightleftharpoons> atom a) \<bullet> t') ((atom y' \<rightleftharpoons> atom b) \<bullet> s') ((a, b) # xs)" in trans)
  apply (rule_tac s="(atom y' \<rightleftharpoons> atom b) \<bullet> aux ((atom x' \<rightleftharpoons> atom a) \<bullet> t') s' ((a, y') # xs)" in trans)
  apply (rule permute_pure[symmetric])
  apply (simp add: eqvts swap_fresh_fresh)
  apply (simp add: lam.fresh fresh_at_base fresh_Pair_elim swap_fresh_fresh)
  apply (subst permute_eqvt)
  apply (simp add: eqvts swap_fresh_fresh)
  apply (subgoal_tac "(atom x' \<rightleftharpoons> atom a) \<bullet> t' = (atom x \<rightleftharpoons> atom a) \<bullet> t")
  apply (subgoal_tac "(atom y' \<rightleftharpoons> atom b) \<bullet> s' = (atom y \<rightleftharpoons> atom b) \<bullet> s")
  apply simp
  apply (subgoal_tac "Lam [y]. s = Lam [b]. ((atom y \<rightleftharpoons> atom b) \<bullet> s)")
  apply (subgoal_tac "Lam [y']. s' = Lam [b]. ((atom y' \<rightleftharpoons> atom b) \<bullet> s')")
  apply (auto simp add: fresh_Pair_elim Abs1_eq_iff)[1]
  apply (rule sym)
  apply (simp add: Abs1_eq_iff fresh_Pair_elim fresh_at_base swap_commute)
  apply (rule sym)
  apply (simp add: Abs1_eq_iff fresh_Pair_elim fresh_at_base swap_commute)
  apply (subgoal_tac "Lam [x]. t = Lam [a]. ((atom x \<rightleftharpoons> atom a) \<bullet> t)")
  apply (subgoal_tac "Lam [x']. t' = Lam [a]. ((atom x' \<rightleftharpoons> atom a) \<bullet> t')")
  apply (auto simp add: fresh_Pair_elim Abs1_eq_iff)[1]
  apply (rule sym)
  apply (simp add: Abs1_eq_iff fresh_Pair_elim fresh_at_base swap_commute)
  apply (rule sym)
  apply (simp add: Abs1_eq_iff fresh_Pair_elim fresh_at_base swap_commute)
  apply (rule refl)
  done

lemma aux_induct:  "\<lbrakk>\<And>xs n m. P xs (Var n) (Var m); \<And>xs n l r. P xs (Var n) (App l r);
 \<And>xs n x t. P xs (Var n) (Lam [x]. t);
 \<And>xs l r n. P xs (App l r) (Var n);
 (\<And>xs l1 r1 l2 r2. P xs l1 l2 \<Longrightarrow> P xs r1 r2 \<Longrightarrow> P xs (App l1 r1) (App l2 r2));
 \<And>xs l r x t. P xs (App l r) (Lam [x]. t);
 \<And>xs x t n. P xs (Lam [x]. t) (Var n);
 \<And>xs x t l1 r1. P xs (Lam [x]. t) (App l1 r1);
 \<And>x xs y s t.
    atom x \<sharp> (xs, Lam [y]. s) \<and>
    atom y \<sharp> (x, xs, Lam [x]. t) \<Longrightarrow> P ((x, y) # xs) t s \<Longrightarrow> P xs (Lam [x]. t) (Lam [y]. s)\<rbrakk>
\<Longrightarrow> P (a :: (name \<times> name) list) b c"
  apply (induction_schema)
  apply (rule_tac y="b" and c="(a, c)" in lam.strong_exhaust)
  apply (rule_tac y="c" and c="(name, a, b)" in lam.strong_exhaust)
  apply simp_all[3] apply (metis)
  apply (rule_tac y="c" and c="(name, a, b)" in lam.strong_exhaust)
  apply simp_all[3] apply (metis, metis, metis)
  apply (rule_tac y="c" and c="(name, a, b)" in lam.strong_exhaust)
  apply simp_all[3] apply (metis)
  apply (simp add: fresh_star_def)
  apply metis
  apply lexicographic_order
  done

nominal_function swapequal :: "lam \<Rightarrow> lam \<Rightarrow> (name \<times> name) list \<Rightarrow> bool" where
  "swapequal l r [] \<longleftrightarrow> l = r"
| "atom x \<sharp> (l, r, hl, hr, t) \<Longrightarrow>
    swapequal l r ((hl, hr) # t) \<longleftrightarrow> swapequal ((hl \<leftrightarrow> x) \<bullet> l) ((hr \<leftrightarrow> x) \<bullet> r) t"
  unfolding eqvt_def swapequal_graph_def
  apply (rule, perm_simp, rule, rule TrueI)
  apply (case_tac x)
  apply (case_tac c)
  apply metis
  apply (case_tac aa)
  apply (rename_tac l r lst h t hl hr)
  apply (rule_tac x="(l, r, hl, hr, t)" and ?'a="name" in obtain_fresh)
  apply simp
  apply simp
  apply simp
  apply clarify
  apply (rule_tac s="(x \<leftrightarrow> xa) \<bullet> swapequal_sumC ((hla \<leftrightarrow> x) \<bullet> la, (hra \<leftrightarrow> x) \<bullet> ra, ta)" in trans)
  apply (simp only: permute_pure)
  apply (simp add: eqvt_at_def fresh_Pair_elim)
  apply (simp add: flip_fresh_fresh)
  apply (subgoal_tac "(x \<leftrightarrow> xa) \<bullet> (hla \<leftrightarrow> x) \<bullet> la = (hla \<leftrightarrow> xa) \<bullet> la")
  apply (subgoal_tac "(x \<leftrightarrow> xa) \<bullet> (hra \<leftrightarrow> x) \<bullet> ra = (hra \<leftrightarrow> xa) \<bullet> ra")
  apply simp
  apply (subst permute_eqvt)
  apply (simp add: flip_fresh_fresh flip_eqvt)
  apply (subst permute_eqvt)
  apply (simp add: flip_fresh_fresh flip_eqvt)
  done

nominal_termination (eqvt) by lexicographic_order

lemma var_eq_swapequal: "atom ab \<sharp> xs \<Longrightarrow> swapequal (Var ab) (Var ab) xs"
  apply (induct xs)
  apply simp
  apply (case_tac a)
  apply (simp add: fresh_Cons)
  apply (rule_tac x="(ab, aa, b, xs)" and ?'a="name" in obtain_fresh)
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair lam.fresh)
  apply (simp add: fresh_Pair_elim)
  by (metis flip_at_base_simps(3) fresh_Pair fresh_at_base(2))

lemma var_neq_swapequal:
  "atom ab \<sharp> xs \<Longrightarrow> ab \<noteq> m \<Longrightarrow> \<not> swapequal (Var ab) (Var m) xs"
  "atom ab \<sharp> xs \<Longrightarrow> ab \<noteq> m \<Longrightarrow> \<not> swapequal (Var m) (Var ab) xs"
  apply (induct xs arbitrary: m)
  apply simp_all[2]
  apply (case_tac [!] a)
  apply (simp_all add: fresh_Cons)
  apply (rule_tac [!] x="(ab, aa, b, m, xs)" and ?'a="name" in obtain_fresh)
  apply (subst swapequal.simps)
  apply (auto simp add: fresh_Pair lam.fresh)[1]
  apply (elim conjE)
  apply (simp add: fresh_Pair_elim fresh_at_base permute_flip_at)
  apply (subst swapequal.simps)
  apply (auto simp add: fresh_Pair lam.fresh)[1]
  apply (elim conjE)
  apply (simp add: fresh_Pair_elim fresh_at_base permute_flip_at)
  done

lemma lookup_swapequal: "lookup n m xs = swapequal (Var n) (Var m) xs"
  apply (induct xs arbitrary: m n)
  apply simp
  apply (case_tac a)
  apply (rule_tac x="(n, m, aa, b, xs)" and ?'a="name" in obtain_fresh)
  apply simp
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair lam.fresh fresh_Nil)
  by (metis (hide_lams, mono_tags) flip_at_base_simps(3) flip_at_simps(1) fresh_Pair fresh_at_base(2) lam.perm_simps(1) var_eq_swapequal var_neq_swapequal(1) var_neq_swapequal(2))

lemma swapequal_reorder: "
  a \<noteq> x \<Longrightarrow> a \<noteq> y \<Longrightarrow> b \<noteq> x \<Longrightarrow> b \<noteq> y \<Longrightarrow>
  swapequal t s ((x, y) # (a, b) # xs) = swapequal t s ((a, b) # (x, y) # xs)"
  apply (rule_tac x="(a, b, x, y, t, s, xs)" and ?'a="name" in obtain_fresh)
  apply (rule_tac x="(a, b, x, y, t, s, xs, aa)" and ?'a="name" in obtain_fresh)
  apply (rename_tac f g)
  apply (simp add: fresh_Pair_elim fresh_at_base)
  apply (subst swapequal.simps)
  apply (auto simp add: fresh_Pair fresh_Cons fresh_at_base)[1]
  apply (subgoal_tac "(x \<leftrightarrow> f) \<bullet> atom g \<sharp> t")
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair fresh_Cons fresh_permute_left)
  apply rule apply assumption
  apply (simp add: flip_at_base_simps fresh_at_base flip_def)
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base)
  apply rule apply (rotate_tac 12)
  apply assumption
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base)
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair fresh_Cons fresh_at_base fresh_permute_left)
  apply (subgoal_tac "(a \<leftrightarrow> g) \<bullet> atom f \<sharp> t")
  apply rule apply assumption
  apply (simp add: flip_at_base_simps fresh_at_base flip_def)
  apply (simp add: flip_at_base_simps fresh_at_base flip_def)
  apply (subgoal_tac "(a \<leftrightarrow> g) \<bullet> (x \<leftrightarrow> f) \<bullet> t = (x \<leftrightarrow> f) \<bullet> (a \<leftrightarrow> g) \<bullet> t")
  apply (subgoal_tac "(b \<leftrightarrow> g) \<bullet> (y \<leftrightarrow> f) \<bullet> s = (y \<leftrightarrow> f) \<bullet> (b \<leftrightarrow> g) \<bullet> s")
  apply simp
  apply (subst permute_eqvt) apply (simp add: flip_eqvt)
  apply (subst permute_eqvt) apply (simp add: flip_eqvt)
  apply (simp add: flip_at_base_simps fresh_at_base flip_def)
  done

lemma swapequal_lambda:
  assumes "distinct xs \<and> atom x \<sharp> xs \<and> atom y \<sharp> xs"
  shows "swapequal (Lam [x]. t) (Lam [y]. s) xs = swapequal t s ((x, y) # xs)"
  using assms
  apply (induct xs arbitrary: t s x y)
  apply (rule_tac x="(x, y, t, s)" and ?'a="name" in obtain_fresh)
  apply (simp add: fresh_Pair_elim fresh_Nil)
  apply (subst swapequal.simps)
  apply (simp add: fresh_Pair fresh_Nil)
  apply auto[1]
  apply simp
  apply (subgoal_tac "[[atom x]]lst. t = [[atom a]]lst. ((x \<leftrightarrow> a) \<bullet> t)")
  apply (subgoal_tac "[[atom y]]lst. s = [[atom a]]lst. ((y \<leftrightarrow> a) \<bullet> s)")
  apply simp
  apply (simp add: Abs1_eq_iff)
  apply (auto simp add: Abs1_eq_iff flip_def fresh_at_base)[2]
  apply (simp add: fresh_permute_left)
  apply (simp add: fresh_permute_left)
  apply clarify
  apply (simp add: fresh_Cons fresh_Pair fresh_at_base)
  apply clarify
  apply (simp add: swapequal_reorder)
  apply (rule_tac x="(x, y, t, s, a, b, xs)" and ?'a="name" in obtain_fresh)
  apply (rename_tac f)
  apply (subst (2) swapequal.simps)
  apply (auto simp add: lam.fresh fresh_Pair fresh_at_base fresh_Cons)[1]
  apply (subst swapequal.simps)
  apply (auto simp add: lam.fresh fresh_Pair fresh_at_base fresh_Cons)[1]
  apply (simp add: flip_def fresh_Pair_elim fresh_at_base)
  done

lemma distinct_swapequal: "\<forall>p q. p \<bullet> l \<noteq> q \<bullet> r \<Longrightarrow> \<not>swapequal l r xs"
  apply (induct xs rule:swapequal.induct)
  apply auto[1]
  apply (simp add: fresh_Pair_elim)
  apply (subgoal_tac "\<forall>(p\<Colon>perm) q\<Colon>perm. p \<bullet> (hl \<leftrightarrow> x) \<bullet> l \<noteq> q \<bullet> (hr \<leftrightarrow> x) \<bullet> r")
  apply simp
  apply (intro allI)
  apply (drule_tac x="p + (hl \<leftrightarrow> x)" in spec)
  apply (drule_tac x="q + (hr \<leftrightarrow> x)" in spec)
  apply simp
  done

lemma swapequal_app: "(swapequal l1 l2 xs \<and> swapequal r1 r2 xs) = swapequal (App l1 r1) (App l2 r2) xs"
  apply (induct xs arbitrary: l1 l2 r1 r2)
  apply simp
  apply (case_tac a)
  apply simp
  apply (rule_tac x="(l1, l2, r1, r2, aa, b, xs)" and ?'a="name" in obtain_fresh)
  apply (simp add: fresh_Pair_elim)
  apply (subst swapequal.simps) apply (auto simp add: fresh_Pair)[1]
  apply (subst swapequal.simps) apply (auto simp add: fresh_Pair lam.fresh)
  done

lemma [simp]: "distinct (map fst xs) \<Longrightarrow> distinct xs"
  by (induct xs) auto

lemma [simp]:
  "atom x \<sharp> xs \<Longrightarrow> x \<notin> fst ` set xs"
  "atom x \<sharp> xs \<Longrightarrow> x \<notin> snd ` set xs"
  apply (induct xs)
  apply simp_all
  apply (case_tac [!] a)
  apply (simp_all add: fresh_Cons fresh_Pair fresh_at_base)
  done

lemma aux_alphaish:
  assumes "distinct (map fst xs @ map snd xs)"
  shows "aux x y xs \<longleftrightarrow> swapequal x y xs"
  using assms
  apply (induct xs x y rule: aux_induct)
  apply (simp add: lookup_swapequal)
  apply (simp, rule distinct_swapequal, simp)+
  apply (simp add: swapequal_app)
  apply (simp, rule distinct_swapequal, simp)+
  apply (simp add: fresh_Pair_elim lam.fresh fresh_at_base conjE)
  apply (elim conjE)
  apply (simp add: fresh_Pair_elim lam.fresh fresh_at_base)
  apply (subgoal_tac "x \<notin> fst ` set xs \<and>
        x \<notin> snd ` set xs \<and> y \<notin> snd ` set xs \<and> y \<notin> fst ` set xs")
  apply (subst swapequal_lambda)
  apply auto[2]
  apply simp
  done

lemma aux_is_alpha:
  "aux x y [] \<longleftrightarrow> (x = y)"
  by (simp_all add: supp_Nil aux_alphaish)

end



