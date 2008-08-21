:- module(intensionalExampleModels,[example/2]).


/*========================================================================
   Example Models

   model(Individuals,Worlds,AccessibleRelations).
========================================================================*/

example(1,model([d1,d2,d3,d4,d5]
	, [ (w0,world(
		[ f(0,mia,d1)
		, f(0,vincent,d2)
		, f(0,pumpkin,d3)
		, f(0,honey_bunny,d4)
		, f(0,yolanda,d5)
		, f(1,snort,[d1])
		, f(1,customer,[d1,d2])
		, f(1,robber,[d3,d4])
		, f(2,love,[(d3,d4)])
		]))
	  , (w1,world(
		[ f(1,snort,[d2])
		, f(2,love,[(d2,d5)])
		]))
	  ]
	, [(d1,w2)]
	))
	.
