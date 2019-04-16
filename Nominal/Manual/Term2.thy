theory Term2
imports "Nominal2_Atoms" "Nominal2_Eqvt" "Nominal2_Supp" "Abs" "Perm" "Fv" "Rsp" "../Attic/Prove"
begin

atom_decl name

section {*** lets with single assignments ***}

datatype rtrm2 =
  rVr2 "name"
| rAp2 "rtrm2" "rtrm2"
| rLm2 "name" "rtrm2" --"bind (name) in (rtrm2)"
| rLt2 "rassign" "rtrm2" --"bind (bv2 rassign) in (rtrm2)"
and rassign =
  rAs "name" "rtrm2"

(* to be given by the user *)
primrec
  rbv2
where
  "rbv2 (rAs x t) = {atom x}"

setup {* snd o define_raw_perms (Datatype.the_info @{theory} "Term2.rtrm2") 2 *}

local_setup {* snd o define_fv_alpha (Datatype.the_info @{theory} "Term2.rtrm2")
  [[[],
    [],
    [(NONE, 0, 1)],
    [(SOME @{term rbv2}, 0, 1)]],
   [[]]] *}

notation
  alpha_rtrm2 ("_ \<approx>2 _" [100, 100] 100) and
  alpha_rassign ("_ \<approx>2b _" [100, 100] 100)
thm alpha_rtrm2_alpha_rassign.intros

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha2_inj}, []), (build_alpha_inj @{thms alpha_rtrm2_alpha_rassign.intros} @{thms rtrm2.distinct rtrm2.inject rassign.distinct rassign.inject} @{thms alpha_rtrm2.cases alpha_rassign.cases} ctxt)) ctxt)) *}
thm alpha2_inj

lemma alpha2_eqvt:
  "t \<approx>2 s \<Longrightarrow> (pi \<bullet> t) \<approx>2 (pi \<bullet> s)"
  "a \<approx>2b b \<Longrightarrow> (pi \<bullet> a) \<approx>2b (pi \<bullet> b)"
sorry

local_setup {* (fn ctxt => snd (Local_Theory.note ((@{binding alpha2_equivp}, []),
  (build_equivps [@{term alpha_rtrm2}, @{term alpha_rassign}] @{thm rtrm2_rassign.induct} @{thm alpha_rtrm2_alpha_rassign.induct} @{thms rtrm2.inject rassign.inject} @{thms alpha2_inj} @{thms rtrm2.distinct rassign.distinct} @{thms alpha_rtrm2.cases alpha_rassign.cases} @{thms alpha2_eqvt} ctxt)) ctxt)) *}
thm alpha2_equivp

local_setup  {* define_quotient_type 
  [(([], @{binding trm2}, NoSyn), (@{typ rtrm2}, @{term alpha_rtrm2})),
   (([], @{binding assign}, NoSyn), (@{typ rassign}, @{term alpha_rassign}))]
  ((rtac @{thm alpha2_equivp(1)} 1) THEN (rtac @{thm alpha2_equivp(2)}) 1) *}

local_setup {*
(fn ctxt => ctxt
 |> snd o (Quotient_Def.quotient_lift_const ("Vr2", @{term rVr2}))
 |> snd o (Quotient_Def.quotient_lift_const ("Ap2", @{term rAp2}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lm2", @{term rLm2}))
 |> snd o (Quotient_Def.quotient_lift_const ("Lt2", @{term rLt2}))
 |> snd o (Quotient_Def.quotient_lift_const ("As", @{term rAs}))
 |> snd o (Quotient_Def.quotient_lift_const ("fv_trm2", @{term fv_rtrm2}))
 |> snd o (Quotient_Def.quotient_lift_const ("bv2", @{term rbv2})))
*}
print_theorems

local_setup {* snd o prove_const_rsp @{binding fv_rtrm2_rsp} [@{term fv_rtrm2}, @{term fv_rassign}]
  (fn _ => fvbv_rsp_tac @{thm alpha_rtrm2_alpha_rassign.induct} @{thms fv_rtrm2_fv_rassign.simps} 1) *}
local_setup {* snd o prove_const_rsp @{binding rbv2_rsp} [@{term rbv2}]
  (fn _ => fvbv_rsp_tac @{thm alpha_rtrm2_alpha_rassign.inducts(2)} @{thms rbv2.simps} 1) *}
local_setup {* snd o prove_const_rsp @{binding rVr2_rsp} [@{term rVr2}]
  (fn _ => constr_rsp_tac @{thms alpha2_inj} @{thms fv_rtrm2_rsp} @{thms alpha2_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rAp2_rsp} [@{term rAp2}]
  (fn _ => constr_rsp_tac @{thms alpha2_inj} @{thms fv_rtrm2_rsp} @{thms alpha2_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rLm2_rsp} [@{term rLm2}]
  (fn _ => constr_rsp_tac @{thms alpha2_inj} @{thms fv_rtrm2_rsp} @{thms alpha2_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding rLt2_rsp} [@{term rLt2}]
  (fn _ => constr_rsp_tac @{thms alpha2_inj} @{thms fv_rtrm2_rsp rbv2_rsp} @{thms alpha2_equivp} 1) *}
local_setup {* snd o prove_const_rsp @{binding permute_rtrm2_rsp} [@{term "permute :: perm \<Rightarrow> rtrm2 \<Rightarrow> rtrm2"}]
  (fn _ => asm_simp_tac (HOL_ss addsimps @{thms alpha2_eqvt}) 1) *}

end
