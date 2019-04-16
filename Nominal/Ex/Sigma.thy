theory Sigma
imports Nominal2
begin

atom_decl name

nominal_datatype obj =
  Var name
| Obj smlst
| Inv obj string
| Upd obj string method
and smlst =
  SMNil
| SMCons string method smlst
and method =
  Sig n::name o::obj binds n in o


end

