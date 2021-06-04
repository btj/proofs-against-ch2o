Require Export ch2o.abstract_c.frontend.
Require Export String.

Local Open Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSLocal [] "i" (CTInt (CIntType None CIntRank))
        (Some
          (CSingleInit
            (CEConst (CIntType (Some Signed) CIntRank) 2000000000)))
        (CSComp
          (CSWhile (CEVar "i")
            (CSDo
              (CEAssign Assign (CEVar "i")
                (CEBinOp (ArithOp MinusOp) (CEVar "i")
                  (CEConst (CIntType (Some Signed) CIntRank) 1)))))
          (CSReturn (Some (CEConst (CIntType (Some Signed) CIntRank) 0))))))].
