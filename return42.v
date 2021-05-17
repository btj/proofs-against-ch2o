Require Export String.
Require Export ch2o.abstract_c.frontend.

Open Local Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSReturn (Some (CEConst (CIntType (Some Signed) CIntRank) 42))))].


