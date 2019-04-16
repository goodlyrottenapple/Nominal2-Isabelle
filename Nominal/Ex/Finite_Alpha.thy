theory Finite_Alpha
imports "../Nominal2"
begin

lemma
  assumes "(supp x - as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> as = bs"
    shows "(as, x) \<approx>set (op =) supp p (bs, y)"
  using assms unfolding alphas
  apply(simp)
  apply(clarify)
  apply(simp only: Diff_eqvt[symmetric] supp_eqvt[symmetric])
  apply(simp only: atom_set_perm_eq)
  done


lemma
  assumes "(supp x - set as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> as = bs"
    shows "(as, x) \<approx>lst (op =) supp p (bs, y)"
  using assms unfolding alphas
  apply(simp)
  apply(clarify)
  apply(simp only: set_eqvt[symmetric] Diff_eqvt[symmetric] supp_eqvt[symmetric])
  apply(simp only: atom_set_perm_eq)
  done

lemma
  assumes "(supp x - as) \<sharp>* p"
      and "p \<bullet> x = y"
      and "p \<bullet> (as \<inter> supp x) = bs \<inter> supp y"
      and "finite (supp x)"
  shows "(as, x) \<approx>res (op =) supp p (bs, y)"
  using assms
  unfolding alpha_res_alpha_set
  unfolding alphas
  apply simp
  apply rule
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric, of _ p])
  apply (simp add: supp_finite_atom_set fresh_star_def)
  apply(auto)[1]
  apply(simp only: Diff_eqvt inter_eqvt supp_eqvt)
  apply (simp add: fresh_star_def)
  apply blast
  done

lemma
  assumes "(as, x) \<approx>res (op =) supp p (bs, y)"
  shows "(supp x - as) \<sharp>* p"
    and "p \<bullet> (as \<inter> supp x) = bs \<inter> supp y"
    and "p \<bullet> x = y"
  using assms
  apply -
  prefer 3
  apply (auto simp add: alphas)[2]
  unfolding alpha_res_alpha_set
  unfolding alphas
  by blast

(* On the raw level *)

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam"
| Lam x::"name" l::"lam"  binds x in l ("Lam [_]. _" [100, 100] 100)

thm alpha_lam_raw.intros(3)[unfolded alphas, simplified]

lemma alpha_fv: "alpha_lam_raw l r \<Longrightarrow> fv_lam_raw l = fv_lam_raw r"
  by (induct rule: alpha_lam_raw.induct) (simp_all add: alphas)

lemma finite_fv_raw: "finite (fv_lam_raw l)"
  by (induct rule: lam_raw.induct) (simp_all add: supp_at_base)

lemma "(fv_lam_raw l - {atom n}) \<sharp>* p \<Longrightarrow> alpha_lam_raw (p \<bullet> l) r \<Longrightarrow>
  fv_lam_raw l - {atom n} = fv_lam_raw r - {atom (p \<bullet> n)}"
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric])
  apply (subst supp_finite_atom_set)
  apply (rule finite_Diff)
  apply (rule finite_fv_raw)
  apply assumption
  apply (simp add: eqvts)
  apply (subst alpha_fv)
  apply assumption
  apply (rule)
  done

(* For the res binding *)

nominal_datatype ty2 =
  Var2 "name"
| Fun2 "ty2" "ty2"

nominal_datatype tys2 =
  All2 xs::"name fset" ty::"ty2" binds (set+) xs in ty

lemma alpha_fv': "alpha_tys2_raw l r \<Longrightarrow> fv_tys2_raw l = fv_tys2_raw r"
  by (induct rule: alpha_tys2_raw.induct) (simp_all add: alphas)

lemma finite_fv_raw': "finite (fv_tys2_raw l)"
  by (induct rule: tys2_raw.induct) (simp_all add: supp_at_base finite_supp)

thm alpha_tys2_raw.intros[unfolded alphas, simplified]

lemma "(supp x - atom ` (fset as)) \<sharp>* p \<Longrightarrow> p \<bullet> (x :: tys2) = y \<Longrightarrow>
  p \<bullet> (atom ` (fset as) \<inter> supp x) = atom ` (fset bs) \<inter> supp y \<Longrightarrow>
  supp x - atom ` (fset as) = supp y - atom ` (fset bs)"
  apply (rule trans)
  apply (rule supp_perm_eq[symmetric])
  apply (subst supp_finite_atom_set)
  apply (rule finite_Diff)
  apply (rule finite_supp)
  apply assumption
  apply (simp add: eqvts)
  apply blast
  done

end
