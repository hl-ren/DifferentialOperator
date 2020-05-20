(* ::Package:: *)

(*Load package*)
(*Get[NotebookDirectory[]<>"dOp5.m"]*)
(**)


(* Wolfram Language Package *)

(* Created by the Wolfram Workbench Dec 25, 2017 *)

(* modified from Carl Wolf, add matrix operation on operators *)
(*dOp->DifferentialOperator, op->operator*)
BeginPackage["dOp`"]
(* Exported symbols added here with SymbolName::usage *) 
Unprotect @@ Names["dOp`*"];
ClearAll @@ Names["dOp`*"];
dOp::usage = "dOp[x__] is equivalent to D[#, xx]&, but it shouldn't need to be used"
SetAttributes[dOp,{Orderless}];

AutoOperator[]:=CurrentValue[EvaluationNotebook[], InputAutoReplacements];

Begin["`Private`"]
(* Implementation of the package *)

CurrentValue[EvaluationNotebook[], InputAutoReplacements] = {
	"pd" -> TemplateBox[
		{"\"\[PartialD]\""},
		"Partial",
		DisplayFunction -> (StyleBox[#, ShowStringCharacters->False]&),
		InterpretationFunction -> (
			RowBox[{"dOp`Private`Op", "[", RowBox[{"dOp","[","]"}],"]"}]&
		),
		Editable->False,
		Selectable->False
	],
	ParentList
};

dOp[z__:Global`x][f_] := D[f, z]

dOp /: dOp[z__:Global`x]^n_Integer?Positive := Apply[
	dOp,
	Flatten @ ConstantArray[{z}, n]
]

dOp /: MakeBoxes[dOp[], form_] := InterpretationBox[
	"\[PartialD]", dOp[]
]

(*dOp /: MakeBoxes[dOp[x__], form_] := With[
	{s1=Level[Times@@{x},{1}]},

	InterpretationBox[
		SubscriptBox["\[PartialD]",RowBox @ BoxForm`MakeInfixForm[s1,",", form]],
		dOp[x]
	]
]*)
dOp /: MakeBoxes[dOp[x__], form_] := With[
	{sub = RowBox @ BoxForm`MakeInfixForm[{x},",", form]},

	InterpretationBox[
		SubscriptBox["\[PartialD]",sub],
		dOp[x]
	]
]

(* CenterDot *)
	
(* arithmetic *)
CenterDot[___, 0, ___] = 0;

(*CenterDot[a_, c__] + CenterDot[b_, c__] ^:= CenterDot[a+b,c]*)
a_?scalarQ CenterDot[b_, c___] ^:= CenterDot[a b, c]


SetAttributes[CenterDot,{Flat,OneIdentity}]

(* nested function application *)
CenterDot[a__, b_][x_] := CenterDot[a][CenterDot[b][x]]

(* function application *)
CenterDot[a_Plus][x_] := CenterDot[#][x]&/@a
CenterDot[a_?scalarQ][x_] := a x
CenterDot[a_?scalarQ b_?differentialQ][x_] := a CenterDot[b][x]
CenterDot[d_dOp][x_] := d[x]
CenterDot[d_dOp,a_?scalarQ]:=d[a]+a d
(*CenterDot[d_dOp]:=d*)


(* differential operator simplification *)
CenterDot[dOp[x__],dOp[y__]]:=dOp[x,y]
CenterDot[a1_+a2_,b_]:=CenterDot[a1,b]+CenterDot[a2,b]
CenterDot[a1_,b1_+b2_]:=CenterDot[a1,b1]+CenterDot[a1,b2]
CenterDot[a1_List, b_] := CenterDot[#, b] & /@ a1
CenterDot[a1_, b1_List] := CenterDot[a1, #] & /@ b1
CenterDot[c_?differentialQ,a_?scalarQ b_?differentialQ]:=CenterDot[c][a]b+a CenterDot[c,b]
CenterDot[a_?scalarQ dOp[x__],dOp[y__]]:=a dOp[x,y]
CenterDot[a_?scalarQ b_?differentialQ, c_?scalarQ]:=(a c) b+a CenterDot[b][c]
CenterDot[c_?scalarQ, a_?scalarQ b_?differentialQ]:=(a c) b
CenterDot[c_?scalarQ, a_?scalarQ]:=a c

CenterDot[a_?scalarQ,b_?differentialQ]:=a b
CenterDot[a_?differentialQ,b_?scalarQ]:=CenterDot[a][b]+b a

(*CenterDot[Op[a_],b_]:=CenterDot[a,b]
CenterDot[a_,Op[b_]]:=CenterDot[a,b]
CenterDot[Op[a_List],b_]:=CenterDot[Op[#],b]&/@a
CenterDot[a_,Op[b_List]]:=CenterDot[a,Op[#]]&/@b*)

(*CenterDot[a_List][x_]:=CenterDot[#][x]&/@a*)

(* Op wrapper *)
SetAttributes[Op, {Flat,OneIdentity}]

(* addition *)
Op[a_]+Op[b_] ^:= Op[a+b]
Op[a_]+c_ ^:= Op[a+c]
c_ +Op[a_]^:= Op[c+a]
	
(* scalar multiplication *)
c_?scalarQ Op[a_] ^:= Op[c a]
c_?scalarQ \[CenterDot] Op[a_] ^:= Op[c a]
(*Op[a_]\[CenterDot]c_?scalarQ^:=Op[a][c]+Op[c a]*)
Op[a_] c_?scalarQ^:=Op[c a]
(*(c_?scalarQ Op[a_]) \[CenterDot] c2_?scalarQ ^:=Op[(c c2) a]

c_?scalarQ \[CenterDot] (c2_?scalarQ Op[a_]) ^:=Op[(c c2) a]*)

(*c1_?scalarQ \[CenterDot]c2_?scalarQ =c1 c2*)
	
(* composition *)
Op[a_,b__] := Op[CenterDot[a,b]]
Op[a_]\[CenterDot]Op[b_] ^:= Op[CenterDot[a,b]]
Op[a_]\[CenterDot]c_?scalarQ ^:= Op[CenterDot[a,c]]
Op[a_List] \[CenterDot] c_?scalarQ ^:=Op[#]\[CenterDot]c &/@a

(*Op[a_]\[CenterDot]c_?differentialQ ^:= Op[CenterDot[a,c]]
Op[a_List] \[CenterDot] c_?differentialQ ^:=Op[#]\[CenterDot]c &/@a*)

Op[a_]\[CenterDot]c_ ^:= Op[CenterDot[a,c]]
c_ \[CenterDot] Op[a_] ^:= Op[CenterDot[c,a]]

Op[a_List] \[CenterDot] c_ ^:=Op[#]\[CenterDot]c &/@a
c_ \[CenterDot] Op[a_List] ^:= c\[CenterDot] Op[#] &/@a
	
(* power *)
Op /: Op[a_]^1 := Op[a]
Op /: Op[a_]^n_Integer := Op[CenterDot@@ConstantArray[a,n]]
Op /: Op[a_List]^n_Integer := Op[#]^n&/@a
(*Op /: Op[a_List]^n_List:= MapThread[(Op[#1]^#2)&,{a,n}]*)
(* subscripted nabla *)
Subscript[Op[dOp[]], x__] ^:= Op[dOp[x]]

(* utilities*)
scalarQ = FreeQ[dOp];
differentialQ = Not @* scalarQ;

(* function application *)
Op[0][x_] := 0
Op[a_][x_] := CenterDot[a][x]
Op[a_List][x_]:=Op[#][x]&/@a

Op/:MakeBoxes[Op[a__], form_]:=If[Length@Hold[a]>1,
	StyleBox[MakeBoxes[CenterDot[a], form], Bold],
	StyleBox[MakeBoxes[a, form], Bold]
]
Op/:Part[Op[a_List],x__]:=Op[a[[x]]]
Op/:Part[Op[a_Plus],x__]:=Op[a[[x]]]
Op/:Part[Op[a_Times],x__]:=Op[a[[x]]]
Op/:Length[Op[a_List]]:=Length[a]
Op/:Dimensions[Op[a_List]]:=Dimensions[a]
Op/:Length[Op[a_Plus]]:=Length[a]
Op/:Dimensions[Op[a_Plus]]:=Dimensions[a]
Op/:Length[Op[a_List]]:=Length[a]
Op/:Dimensions[Op[a_Times]]:=Dimensions[a]
Op/:MatrixForm[Op[a_List]]:=Op[MatrixForm[a]]
Op/:TraditionalForm[Op[a_List]]:=Op[TraditionalForm[a]]
Op/:TensorContract[Op[a_List],x__]:=Op[TensorContract[a,x]]
Op/:Tr[Op[a_List]]:=Op[Tr[a]]
Op/:Det[Op[a_List]]:=Op[Det[a]]
Op/:Transpose[Op[a_List]]:=Op[Transpose[a]]
Op/:Reverse[Op[a_List]]:=Op[Reverse[a]]
Op/:Reverse[Op[a_List],n_]:=Op[Reverse[a,n]]
Op/:Flatten[Op[a_List]]:=Op[Flatten[a]]
Op/:Flatten[Op[a_List],n_]:=Op[Flatten[a,n]]
Op/:Variables[Op[a_]]:=Level[Flatten[{a}],{1}]
Op/:Simplify[Op[a_]]:=Op[Simplify[a]]
Op/:Simplify[Op[a_],x_]:=Op[Simplify[a,x]]
Op/:ToString[Op[a_]]:=ToString[a]
Op/:ToString[Op[a_List]]:=ToString[#]&/@a
Op/:ArrayReshape[Op[a_List],ix_]:=Op[ArrayReshape[a,ix]]
Op/:Partition[Op[a_List],ix_]:=Op[Partition[a,ix]]
(*Op/:Collect[Op[a_],x_]:=Op[Collect[a,x]]
Op/:CoefficientList[Op[a_],x_]:=Op[CoefficientList[a,x]]
Op/:Replace[Op[a_],rules_]:=Op[Replace[a,rules]]*)

ToString2[a_List]:=ToString[#]&/@a
ToString2[a_]:=ToString[a]

Op/:Expand[Op[a_]]:=Op[Expand[a]]
(*Op/:ReplaceAll[Op[a_],rules_]:=Op[ReplaceAll[a,rules]]

Op/:ReplaceAll[a_?scalarQ Op[b_],a_\[Rule]a1_]:=a1 Op[b]
Op/:ReplaceAll[a_?scalarQ Op[b_],b_\[Rule]a1_]:=a Op[a1]
Op/:ReplaceAll[a_?scalarQ+ Op[b_],a_\[Rule]a1_]:=a1 +Op[b]
Op/:ReplaceAll[a_?scalarQ+ Op[b_],b_\[Rule]a1_]:=a + Op[a1]*)

Op/:ReplaceAll[Op[a_],rule_]:=
Block[
    {sop,vop,v1,v2,r2},
	vop=Flatten[{rule}];
	v1=vop[[All,1]];v2=vop[[All,2]];
	v1=ToString2[v1];v2=ToString2[v2];
	r2=Rule@@@({v1,v2}\[Transpose]);
	sop=ToString[InputForm[a]];
	sop=StringReplace[sop,r2];
	Op[ToExpression[sop]]
]

(*Op/:ReplaceAll0[Op[a_],rule_, sform_:False]:=Block[{sop,vop,v1,v2,r2},
If[sform,sop=ToString[InputForm[a]];vop=Flatten[{rule}];
v1=vop[[All,1]];v2=vop[[All,2]];v1=ToString2[v1];v2=ToString2[v2];r2=Rule@@@({v1,v2}\[Transpose]);
sop=StringReplace[sop,r2];ToExpression[sop],Op[ReplaceAll[a,rule]]]]*)

(*Op/:Simplify[Op[a_List]]:=Simplify[Op[#]]&/@a
Op/:Simplify[Op[a_]]:=
*)

(* arrays *)

a : {___, _Op, ___} ^:= Op[Block[{Op = Identity}, a]]

a_List \[CircleTimes] b_List=TensorProduct[a,b];
b_ . Op[a_List] ^:= Inner[Op[#1 #2] &, b, a]
b_ \[CircleTimes] Op[a_List] ^:= Outer[Op[#1 #2] &, b,a]
Op[a_List].b_ ^:= Inner[Op[#1][#2] &, a, b]
Op[a_List]\[CircleTimes]b_ ^:= Outer[Op[#1][#2] &, a, b]
Op[a_List].Op[b_List] ^:= Inner[Op@CenterDot[##] &, a, b]
Op[a_List]\[CircleTimes]Op[b_List] ^:= Outer[Op@CenterDot[##] &, a, b]
Op[a_List] Op[b_List] ^:= MapThread[((Op[#1]) (Op[#2]))&,{a,b}]
Op[a_] Op[b_List] ^:= (Op[a] Op[#])&/@b
Op[a_List] Op[b_] ^:= (Op[#] Op[b])&/@a
Op[a_] Op[b_]^:= Op@CenterDot[a,b]

End[]

EndPackage[]
