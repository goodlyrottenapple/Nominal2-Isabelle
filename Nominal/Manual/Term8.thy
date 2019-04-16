theory Term8
imports "../../Nominal-General/Nominal2_Atoms" "../../Nominal-General/Nominal2_Eqvt" "../../Nominal-General/Nominal2_Supp" "../Abs" "../Perm" "../Fv" "../Rsp" "../Lift" "../../Attic/Prove"
begin

atom_decl name

datatype rfoo8 =
  Foo0 "name"
| Foo1 "rbar8" "rfoo8" --"bind bv(bar) in foo"
and rbar8 =
  Bar0 "name"
| Bar1 "name" "name" "rbar8" --"bind second name in b"

primrec
  rbv8
where
  "rbv8 (Bar0 x) = {}"
| "rbv8 (Bar1 v x b) = {atom v}"

setup {* snd o define_raw_perms (Datatype.the_info @{theory} "Term8.rfoo8") 2 *}
print_theorems

ML define_fv_alpha_export
local_setup {* snd o define_fv_alpha_export (Datatype.the_info @{theory} "Term8.rfoo8") [
  [[], [(SOME (@{term rbv8}, false), 0, 1, AlphaGen)]], [[], [(NONE, 1, 2, AlphaGen)]]]
  [(@{term "rbv8"}, 1, [[], [(0, NONE), (2, SOME @{term rbv8})]])] *}
notation
  alpha_rfoo8 ("_ \<approx>f' _" [100, 100] 100) and
  alpha_rbar8 ("_ \<approx>b' _" [100, 100] 100)
thm alpha_rfoo8_alpha_rbar8_alpha_rbv8.intros[no_vars]
thm fv_rbar8.simps fv_rfoo8_fv_rbv8.simps

inductive
  alpha8f :: "rfoo8 \<Rightarrow> rfoo8 \<Rightarrow> bool" ("_ \<approx>f _" [100, 100] 100)
and
  alpha8b :: "rbar8 \<Rightarrow> rbar8 \<Rightarrow> bool" ("_ \<approx>b _" [100, 100] 100)
and
  alpha8bv:: "rbar8 \<Rightarrow> rbar8 \<Rightarrow> bool" ("_ \<approx>bv _" [100, 100] 100)
where
  "name = namea \<Longrightarrow> Foo0 name \<approx>f Foo0 namea"
| "\<exists>pi. rbar8 \<approx>bv rbar8a \<and>
     (rbv8 rbar8, rfoo8) \<approx>gen alpha8f fv_rfoo8 pi (rbv8 rbar8a, rfoo8a) \<Longrightarrow>
  Foo1 rbar8 rfoo8 \<approx>f Foo1 rbar8a rfoo8a"
| "name = namea \<Longrightarrow> Bar0 name \<approx>b Bar0 namea"
| "\<exists>pi. name1 = name1a \<and> ({atom name2}, rbar8) \<approx>gen alpha8b fv_rbv8 pi ({atom name2a}, rbar8a) \<Longrightarrow>
  Bar1 name1 name2 rbar8 \<approx>b Bar1 name1a name2a rbar8a"
| "name = namea \<Longrightarrow> alpha8bv (Bar0 name) (Bar0 namea)"
| "({atom name2}, rbar8) \<approx>gen alpha8b fv_rbv8 pi ({atom name2a}, rbar8a) \<Longrightarrow>
   alpha8bv (Bar1 name1 name2 rbar8) (Bar1 name1a name2a rbar8a)"

lemma "(alpha8b ===> op =) rbv8 rbv8"
  apply rule
  apply (induct_tac a b rule: alpha8f_alpha8b_alpha8bv.inducts(2))
  apply (simp_all)
  done

lemma fv_rbar8_rsp_hlp: "x \<approx>b y \<Longrightarrow> fv_rbar8 x = fv_rbar8 y"
  apply (erule alpha8f_alpha8b_alpha8bv.inducts(2))
  apply (simp_all add: alpha_gen)
  apply clarify
  sorry

lemma "(alpha8b ===> op =) fv_rbar8 fv_rbar8"
  apply simp apply clarify apply (simp add: fv_rbar8_rsp_hlp)
  done

lemma "(alpha8f ===> op =) fv_rfoo8 fv_rfoo8"
  apply simp apply clarify
  apply (erule alpha8f_alpha8b_alpha8bv.inducts(1))
  apply (simp_all add: alpha_gen fv_rbar8_rsp_hlp)

done

end
