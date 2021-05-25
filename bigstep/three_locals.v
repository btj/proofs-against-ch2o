Require Export String.
Require Export ch2o.abstract_c.frontend.

Open Local Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSLocal [] "x" (CTInt (CIntType None CIntRank))
        (Some (CSingleInit (CEConst (CIntType (Some Signed) CIntRank) 1)))
        (CSLocal [] "y" (CTInt (CIntType None CIntRank))
          (Some (CSingleInit (CEConst (CIntType (Some Signed) CIntRank) 2)))
          (CSLocal [] "z" (CTInt (CIntType None CIntRank))
            (Some (CSingleInit (CEVar "x"))) (CSReturn (Some (CEVar "y")))))))].
