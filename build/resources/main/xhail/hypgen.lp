% Inspire Inductive Logic Programming System
% Copyright (C) 2016-2018  Peter Schueller <schueller.p@gmail.com>
%
% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.
%
% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.
%
% You should have received a copy of the GNU General Public License
% along with this program.  If not, see <http://www.gnu.org/licenses/>.

#const maxinventpred = 1.
#const maxuseppred = 2. % positive predicate use, per predicate
#const maxusenpred = 2. % negative predicate use, per predicate
#const maxvars = 4. % overall
#const maxliterals = 4.
#const invent_minarity = 2. % we can represent arity 1 within arity 2 (all atoms are reflexive)
#const invent_maxarity = 2.

#const cost_distinctvariable = 1.
#const free_distinct_variables = 2.
#const cost_variable_boundmorethantwice = 2.
#const cost_type_usedmorethantwice = 2.
#const cost_posbodyliteral = 1.
#const cost_negbodyliteral = 2.
#const cost_pred_multi = 2.
#const cost_binary_reflexive = 5.
#const cost_variable_onlyheadbound = 5.
#const cost_variable_onlyoncebodybound = 5.
#const cost_invent_predicate = 2.
#const cost_invented_predicate = 2.
#const cost_invented_head_and_body = 3.
#const cost_invented_body_multi = 5.
#const cost_invented_head_body_order = 5.

#const maxcost = 10.

% head predicates and args
hpred(I,P,N) :- tpred(I,P,N).
harg(I,J,T) :- targ(I,J,T).

% body predicates and args
% bpred(PredIdentifier,Predicate,NumberOfArguments)
% barg(PredIdentifier,ArgumentPosition,Type)
bpred(I,P,N) :- rpred(I,P,N).
barg(I,J,T) :- rarg(I,J,T).

% which arg types do we have
type(T) :- targ(_,_,T).
type(T) :- rarg(_,_,T).

% create order over type(T)
% each type gets a unique index type_id(T,Idx)
%
type_first(MT) :- MT = #min { T : type(T) }.
type_next(T,TN) :- type(T), TN = #min { X : type(X), X > T }, TN != #sup.
type_last(MT) :- MT = #max { T : type(T) }.
type_id(T,1) :- type_first(T).
type_id(T2,ID+1) :- type_id(T1,ID), type_next(T1,T2).

typecount(TC) :- TC = #count { 1,T : type(T) }.

% this does not work: if we invent 2 predicates, we must be able to freely choose!
%% how many predicates to invent
%1 { ipredcount(0..maxinventpred) } 1 :- maxinventpred > 0.
%% whether to invent predicate with identity Id and arity A
%1 { ipred(ip(Id,A),A) : A = invent_minarity..invent_maxarity } 1 :- ipredcount(IP), Id = 1..IP.
%cost(ipred,Id,cost_invented_predicate) :- ipred(Id,Arity).
% hence the following
% guess at most one arity for each predicate to invent
0 { ipred(ip(Id,A),A) : A = invent_minarity..invent_maxarity } 1 :- Id = 1..maxinventpred.
% inventing predicates in general has a cost
cost(invent_pred,dummy,cost_invent_predicate) :- ipred(_,_).
% each invented predicate has a cost
cost(ipred,Id,cost_invented_predicate) :- ipred(Id,Arity).

% argument types of invented predicate
1 { iarg(Id,Pos,T) : type(T) } 1 :- ipred(Id,A), Pos = 1..A.

% symmetry breaking: in invented predicates, argument types are sorted as the types are
:- iarg(Id,Pos1,T1), iarg(Id,Pos2,T2), Pos1 < Pos2, T2 < T1.

% invented predicates are head and body predicates
hpred(Id,Id,A) :- ipred(Id,A).
harg(I,J,T) :- iarg(I,J,T).

bpred(Id,Id,A) :- ipred(Id,A).
barg(I,J,T) :- iarg(I,J,T).

% we create maxvars variables for each type
var_type(v(ID*maxvars+Idx),T) :- type_id(T,ID), Idx=0..(maxvars-1).

% we use some of these variables
1 { varcount(1..maxvars) } 1.
% cost based on number of distinct variables but only above certain count
cost(varcount,dummy,(Count-free_distinct_variables)*cost_distinctvariable) :- varcount(Count), Count > free_distinct_variables.

VC { use_var_type(V,T): var_type(V,T) } VC :- varcount(VC).

% symmetry breaking: use first k variables of same type (not select freely k variables of same type)
%
% if we use one variable of one type, we also have to use the next lower one of same type
use_var_type(v(Id-1),Type) :- use_var_type(v(Id),Type), var_type(v(Id-1),Type).

% cost for types that appear more than twice
cost(vartype_morethantwice,Type,cost_type_usedmorethantwice*(NUse-2)) :-
  NUse > 2, NUse = #count { Id : use_var_type(v(Id),Type) }, type_id(Type,_).

% we create for each predicate maxusepred literals in the body
body_pred(id_idx(Id,Idx),Pred,pos,Arity) :- bpred(Id,Pred,Arity), Idx = 1..maxuseppred.
body_pred(id_idx(Id,Idx),Pred,neg,Arity) :- bpred(Id,Pred,Arity), Idx = 1..maxusenpred.

% we use some of these literals
1 { use_body_pred(id_idx(Id,Idx),Pred,Polarity,Arity) : body_pred(id_idx(Id,Idx),Pred,Polarity,Arity) } maxliterals.
cost(pbodyliteral,IdIdx,cost_posbodyliteral) :- use_body_pred(IdIdx,_,pos,_).
cost(nbodyliteral,IdIdx,cost_negbodyliteral) :- use_body_pred(IdIdx,_,neg,_).

% symmetry breaking: use first k predicates of same type (not select freely k predicates of same type)
%
% if we use one predicates of one type, we also have to use the next lower one of same type
use_body_pred(id_idx(PredId,Idx-1),Pred,Polarity,Arity) :- use_body_pred(id_idx(PredId,Idx),Pred,Polarity,Arity), Idx > 1.

cost(pred_multi,id_idx(Pred,Idx),cost_pred_multi) :- use_body_pred(id_idx(Pred,Idx),_,_,_), Idx > 1.

% we use one head predicate
1 { use_head_pred(Id,Pred,NArgs) : hpred(Id,Pred,NArgs) } 1.

% if invented predicate is in head, having same predicate also in body makes additional cost
cost(inv_head_body,ip(Id,A),cost_invented_head_and_body) :-
  use_head_pred(ip(Id,A),_,_), use_body_pred(id_idx(ip(Id,A),Idx),_,_,A).

% if two same invented predicates are in the body, this has additional cost
cost(inv_body_mult,id_idx_idx(ip(Id,A),Idx1,Idx2),cost_invented_body_multi) :-
  use_body_pred(id_idx(ip(Id,A),Idx1),_,_,A), Idx1 < Idx2,
  use_body_pred(id_idx(ip(Id,A),Idx2),_,_,A).

% if one invented predicate is in head, another invented predicate in the body must be smaller or there is cost
cost(inv_head_body_order,h_b(ip(Id1,A1),id_idx(ip(Id2,Idx2))),cost_invented_head_body_order) :-
  use_head_pred(ip(Id1,A1),_,A1), Id1 >= Id2,
  use_body_pred(id_idx(ip(Id2,Idx2),_),_,_,_).

% find out if we use ipred if we have one
use_ipred(Id) :- ipred(Id,_), use_head_pred(Id,_,_).
use_ipred(Id) :- ipred(Id,_), use_body_pred(id_idx(Id,_),_,_,_).
% forbid that we do not use it if we have it
:- ipred(Id,_), not use_ipred(Id).

% we bind variables to argument positions in head and body literals

% for each used head pred for all head argument positions bind one var of correct type
% (if we have no appropriate var in the guess, this eliminates the guess)
1 { bind_hvar(Pos, VId) : use_var_type(VId,Type) } 1 :- use_head_pred(PredId,_,_), harg(PredId,Pos,Type).

% symmetry breaking: if we bind a variable to the head, also bind lower variables of same type to the head
%
% if we use one variable of one type, we also have to use the next lower one of same type
:- bind_hvar(Pos,v(Idx)), var_type(v(Idx),Type), var_type(v(Idx-1),Type), not hbound_var(v(Idx-1)).

% symmetry breaking: if we bind two variables of same type to the head, the lower is bound to the left
:- bind_hvar(1,Idx1), bind_hvar(2,Idx2), var_type(Idx1,Type), var_type(Idx2,Type), Idx1 > Idx2.

% for each used body literal for all argument positions bind one var of correct type
% (if we have no appropriate var in the guess, this eliminates the guess)
1 { bind_bvar(id_idx(PredId,Idx),Polarity,Position,VId) : use_var_type(VId,Type) } 1 :-
  use_body_pred(id_idx(PredId,Idx),_,Polarity,_), barg(PredId,Position,Type).

% symmetry breaking: if we use a predicate twice, the one with lower arguments is first
%
% define variable signature for each literal of arity 2
lit_vsig(Id,Idx,Polarity,1,V) :-
  use_body_pred(id_idx(Id,Idx),_,Polarity,1), bind_bvar(id_idx(Id,Idx),Polarity,1,V).
lit_vsig(Id,Idx,Polarity,2,vv(V1,V2)) :-
  use_body_pred(id_idx(Id,Idx),_,Polarity,2),
  bind_bvar(id_idx(Id,Idx),Polarity,1,V1),
  bind_bvar(id_idx(Id,Idx),Polarity,2,V2).
% if two body predicates have same predicate and polarity but different ID's, enforce a certain order
:- lit_vsig(Id,Idx1,Polarity,Arity,Sig1), lit_vsig(Id,Idx2,Polarity,Arity,Sig2), Idx1 < Idx2, Sig1 > Sig2.

% forbid that we have a variable if we do not bind it

% find out if we bind variable if we have one
hbound_var(VId) :- bind_hvar(_,VId).
pbound_var(VId) :- bind_bvar(_,pos,_,VId).
nbound_var(VId) :- bind_bvar(_,neg,_,VId).
bbound_var(VId) :- pbound_var(VId).
bbound_var(VId) :- nbound_var(VId).

% cost for variables bound only in head
cost(onlyheadbound,VId,cost_variable_onlyheadbound) :- use_var_type(VId,_), hbound_var(VId), not bbound_var(VId).

% we do not forbid unsafe rules (all variables have a type, so all rules are safe)
% forbid variables that are not bound at all
:- use_var_type(VId,_), not hbound_var(VId), not bbound_var(VId).

% cost for variables bound only once in body and not in head
cost(onlyoncebbound,VId,cost_variable_onlyoncebodybound) :- use_var_type(VId,_), not hbound_var(VId), 1 = #count { Pred,Pol : bind_bvar(Pred,Pol,_,VId) }.

% cost for variables bound more than twice in total
cost(var_boundmorethantwice,VId,cost_variable_boundmorethantwice*(NBound-2)) :-
  use_var_type(VId,_), NBound > 2,
  NBound = #count { h,Pos : bind_hvar(Pos,VId) ; b,Pred,Pol,Pos : bind_bvar(Pred,Pol,Pos,VId) }.

% forbid equal literals

% find equal literals (ignore different polarity - it is useless to have foo(X) and not foo(X) in the same body)
litequal_upto(Idx1,Idx2,Polarity1,Polarity2,0,Arity) :-
  use_body_pred(Idx1,Pred,Polarity1,Arity),
  use_body_pred(Idx2,Pred,Polarity2,Arity), (Idx1, Polarity1) < (Idx2, Polarity2).
litequal_upto(Idx1,Idx2,Polarity1,Polarity2,Upto+1,Arity) :- litequal_upto(Idx1,Idx2,Polarity1,Polarity2,Upto,Arity),
  Upto < Arity, bind_bvar(Idx1,Polarity1,Upto+1,VId), bind_bvar(Idx2,Polarity2,Upto+1,VId).
litequal(Idx1,Idx2) :- litequal_upto(Idx1,Idx2,_,_,Arity,Arity).
% forbid equal literals
:- litequal(Idx1,Idx2).


% forbid reflexive variable binding for binary predicates if literals are nonreflexive (e.g., adjacent)
reflexive(id_idx(PredId,Idx),Polarity) :- use_body_pred(id_idx(PredId,Idx),Pred,Polarity,2),
  bind_bvar(id_idx(PredId,Idx),Polarity,1,VId), bind_bvar(id_idx(PredId,Idx),Polarity,2,VId).
:- reflexive(id_idx(PredId,_),_), nonreflexive(PredId).
cost(binary_reflexive,id_idx_pol(PredId,Idx,Polarity),cost_binary_reflexive) :- reflexive(id_idx(PredId,Idx),Polarity).

% forbid half of the variable bindings where first variable is larger than second if literals are symmetric (e.g., adjacent)
:- use_body_pred(id_idx(PredId,Idx),Pred,Pol,2), symmetric(PredId),
  bind_bvar(id_idx(PredId,Idx),Polarity,1,VId1), VId1 > VId2,
  bind_bvar(id_idx(PredId,Idx),Polarity,2,VId2).

% eliminate warnings
symmetric(X) :- symmetric(X).
nonreflexive(X) :- nonreflexive(X).

% represent true total cost only if it is below maxcost
totalcost(C) :- C = #sum { Cost,U,V : cost(U,V,Cost) }, C < maxcost.
% represent maximum cost for costs above
totalcost(maxcost) :- maxcost <= #sum { Cost,U,V : cost(U,V,Cost) }.
% the following would explode the grounding
%totalcost(C) :- C = #sum { Cost,U,V : cost(U,V,Cost) }.

:- totalcost(C), C >= maxcost.
%:- not totalcost(8).
%#show cost/3.

%#show.
%%#show hpred/3.
%%#show harg/3.
%#show ipred/2.
%#show iarg/3.
%%#show bpred/3.
%%#show barg/3.
%%#show type_id/2.
%#show use_var_type/2.
%#show use_body_pred/3.
%#show use_head_pred/3.
%#show bind_hvar/2.
%#show bind_bvar/3.
%
