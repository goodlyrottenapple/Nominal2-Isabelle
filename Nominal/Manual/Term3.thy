theory Term3
imports "Nominal2_Atoms" "Nominal2_Eqvt" "Nominal2_Supp" "Abs" "Perm" "Fv" "Rsp" "../Attic/Prove"
begin

atom_decl name

section {*** lets with many assignments ***}

datatype rtrm3 =
  rVr3 "name"
| rAp3 "rtrm3" "rtrm3"
| rLm3 "name" "rtrm3" --"bind (name) in (trm3)"
| rLt3 "rassigns" "rtrm3" --"bind (bv3 assigns) in (trm3)"
and rassigns =
  rANil
| rACons "name" "rtrm3" "rassigns"

(* to be given by the user *)
primrec 
  bv3
where
  "bv3 rANil = {}"
| "bv3 (rACons x t as) = {atom x} \<union> (bv3 as)"

setup {* snd o define_raw_perms (Datatype.the_info @{theory} "Term3.rtrm3") 2 *}

local_setup {* snd o define_fv_alpha (Datatype.the_info @{theory} "Term3.rtrm3")
  [[[[]], [[], []], [[(NONE, 0)], [(NONE, 0)]], [[], [(SOME @{term bv3}, 0)]]],
   [[], [[], [], []]]] *}
print_theorems

notation
  alpha_rtrm3 ("_ \<approx>3 _" [100, 100] 100) and
  alpha_rassigns ("_ \<approx>3a _" [100, 100] 100)
thm alpha_rtrm3_alpha_rassigns.intros

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha3_inj}, []), (build_alpha_inj @{thms alpha_rtrm3_alpha_rassigns.intros} @{thms rtrm3.distinct rtrm3.inject rassigns.distinct rassigns.inject} @{thms alpha_rtrm3.cases alpha_rassigns.cases} ctxt)) ctxt)) *}
thm alpha3_inj

lemma alpha3_eqvt:
  "t \<approx>3 s \<Longrightarrow> (pi \<bullet> t) \<approx>3 (pi \<bullet> s)"
  "a \<approx>3a b \<Longrightarrow> (pi \<bullet> a) \<approx>3a (pi \<bullet> b)"
sorry

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha3_equivp}, []),
  (build_equivps [@{term alpha_rtrm3}, @{term alpha_rassigns}] @{thm rtrm3_rassigns.induct} @{thm alpha_rtrm3_alpha_rassigns.induct} @{thms rtrm3.inject rassigns.inject} @{thms alpha3_inj} @{thms rtrm3.distinct rassigns.distinct} @{thms alpha_rtrm3.cases alpha_rassigns.cases} @{thms alpha3_eqvt} ctxt)) ctxt)) *}
thm alpha3_equivp

quotient_type
  trm3 = rtrm3 / alpha_rtrm3
and
  assigns = rassigns / alpha_rassigns
  by (rule alpha3_equivp(1)) (rule alpha3_equivp(2))

end
