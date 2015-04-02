(set-logic QF_AUFDTLIAFS)
(set-option :produce-models true)

(declare-datatypes () ((Func <% _.each(funcs, function(f) { %> (<%=f%>) <% }) %>)))
(declare-datatypes () ((Obj <% _.each(objs, function(o) { %> (<%=o%>) <% }) %>)))
(declare-datatypes () ((Node <% _.each(nodes, function(n) { %> (<%=n%>) <% }) %>)))

(define-sort FuncSet () (Set Func))
(define-sort ObjSet () (Set Obj))
(declare-datatypes () ((Value (Val (funcs FuncSet) (objs ObjSet)))))

(declare-const sol (Array Node Value))

(define-fun hasobj ((n Node) (o Obj)) Bool
  (member o (objs (select sol n))))

(define-fun hasfunc ((n Node) (f Func)) Bool
  (member f (funcs (select sol n))))

(define-fun flow ((from Node) (to Node)) Bool
  (and (subset (funcs (select sol from)) (funcs (select sol to)))
       (subset (objs (select sol from)) (objs (select sol to)))))

<% _.forOwn(objConstraints, function(os,n) { _.each(os, function(o) { %>
(assert (hasobj <%=n%> <%=o%>))
<% }) }) %>

<% _.forOwn(funcConstraints, function(fs,n) { _.each(fs, function(f) {  %>
(assert (hasfunc <%=n%> <%=f%>))
<% }) }) %>

<% _.forOwn(flowConstraints, function(tos,from) { _.each(tos, function(to) { %>
(assert (flow <%=from%> <%=to%>))
<% }) }) %>

(check-sat)
(get-model)
