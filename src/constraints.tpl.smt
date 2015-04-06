(set-logic AUFDTLIAFS)
(set-option :produce-models true)

(declare-datatypes () ((Func <% for(var i = 1; i <= funcs; i++) { %> (F<%=i%>) <% } %>)))
(declare-datatypes () ((Obj <% for(var i = 1; i <= objs; i++) { %> (O<%=i%>) <% } %>)))
(declare-datatypes () ((Var <% for(var i = 1; i <= vars; i++) { %> (V<%=i%>) <% } %>)))
(declare-datatypes () ((Prop <% for(var i = 1; i <= props; i++) { %> (P<%=i%>) <% } %>)))
(declare-datatypes () ((Arg <% for(var i = 1; i <= args; i++) { %> (A<%=i%>) <% } %>)))

(declare-datatypes () ((Node
                         (Var (varname Var))
                         (Res (resf Func))
                         (Arg (argf Func) (argi Arg))
                         (Prop (propobj Obj) (propname Prop)))))

(define-sort FuncSet () (Set Func))
(define-sort ObjSet () (Set Obj))
(declare-datatypes () ((Value (Val (funcs FuncSet) (objs ObjSet)))))

(declare-const sol (Array Node Value))

; n = { ... }
(define-fun hasobj ((n Node) (o Obj)) Bool
  (member o (objs (select sol n))))

; n = function f() { ... }
(define-fun hasfunc ((n Node) (f Func)) Bool
  (member f (funcs (select sol n))))

; to = from
(define-fun flow ((from Node) (to Node)) Bool
  (and (subset (funcs (select sol from)) (funcs (select sol to)))
       (subset (objs (select sol from)) (objs (select sol to)))))

; to = fun()
(define-fun flow-res ((fun Node) (to Node)) Bool
  (forall ((f Func))
      (=> (member f (funcs (select sol fun)))
          (flow (Res f) to))))

; _ = fun( ... a_i ... )
(define-fun flow-arg ((from Node) (fun Node) (arg Arg)) Bool
  (forall ((f Func))
      (=> (member f (funcs (select sol fun)))
          (flow from (Arg f arg)))))

; to = obj.p
(define-fun flow-get ((obj Node) (prop Prop) (to Node)) Bool
  (forall ((o Obj))
      (=> (member o (objs (select sol obj)))
          (flow (Prop o prop) to))))

; obj.p = from
(define-fun flow-set ((from Node) (obj Node) (prop Prop)) Bool
  (forall ((o Obj))
      (=> (member o (objs (select sol obj)))
          (flow from (Prop o prop)))))

<% _.each(constraints, function(c) { %>
(assert <%=c%>)
<% }) %>

(check-sat)
(get-model)
