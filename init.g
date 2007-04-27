#############################################################################
##
#A  init.g                        Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This is the init file of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a
##  GAP package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: init.g,v 1.17 2007/04/27 09:25:17 goetz Exp $
##

#############################################################################
ZIGZAG:= rec();
ZIGZAG.Version:= "0.70";
ZIGZAG.Date:= "13-12-2006";

#############################################################################
##
#R  RequirePackage . . . . . . . . . . . . . . . . . . . . . . . . . require.
##
##  Here is the list of packages  which this package needs as prerequisites.
##
RequirePackage("monoid");
RequirePackage("chevie");

#############################################################################
##
#F  InfoZigzag? . . . . . . . . . . . . . . . . . . . . . . . info functions.
##
if not IsBound(InfoZigzag1) then InfoZigzag1:= Ignore; fi;
if not IsBound(InfoZigzag2) then InfoZigzag2:= Ignore; fi;

#############################################################################
##
#A  AUTO . . . . . . . . . . . . . . . . . . . . . . . . . . . .  auto reads.  
##
AUTO( ReadPkg( "zigzag", "lib", "arrows" ),
  HeadArrow, TailArrow, OnArrows, DeltaArrow, LittleDeltaArrow,
  BigMatrixArrow, ProductArrows, ProductArrowList, FactorsArrow,
  StabilizerArrow, ReversedArrow );

AUTO( ReadPkg( "zigzag", "lib", "bundles" ),
  BundleOps, Bundle, IsBundle, Bundles0, Bundles, NrBundles,
  EssentialBundles, ProductArrowMatrices, ProductArrowMatrixList,
  SumArrowMatrices, DeltaPath, Negative, DeltaPath,
  QuiverRelations0, QuiverRelations, BundleProduct, PrintQuiver,
  DimensionsMatrix, VerifyQuiver );

AUTO( ReadPkg( "zigzag", "lib", "iterator" ),
  IteratorSet, Iterator, IteratorRange );

AUTO( ReadPkg( "zigzag", "lib", "methods" ),
  Call, ApplyMethod, PartitionOps, Partition );

AUTO( ReadPkg( "zigzag", "lib", "shapes" ),
  ShapeOps, Shape, IsShape, NormalizerComplement, ShapesRank,
  Shapes, SubsetsShapes, ComplementsShapes, IncidenceMatShapes,
  CollapsedIncMatShapes, IncMatShapes, FusMatShapes1, FusMatShapes,
  CollapsedFusMatShapes, XCharacters, ParabolicTom, YCharacters,
  ZCharacters, InvolutionShapes, Involutions, SpecialInvolutions,
      OrlikSolomonCharacter, PrimeShapes, NamesShapes, MatrixPath );

AUTO( ReadPkg( "zigzag", "lib", "category" ),
      CategoryOps, Category, CategoryEltOps, CategoryElt );

AUTO( ReadPkg( "zigzag", "lib", "groupoid" ),
      GroupoidOps, Groupoid, GroupoidEltOps, GroupoidElt );

AUTO( ReadPkg( "zigzag", "lib", "subsets" ),
  PrefixesOps, Prefixes, IsPrefixes, WeakIntervalOps, WeakInterval,
  IsWeakInterval, ParabolicTransversalOps, ParabolicTransversal,
  IsParabolicTransversal, DescentClassOps, DescentClass,
  IsDescentClass, DescentClasses, LeftParabolicTransversalOps,
  LeftParabolicTransversal, IsLeftParabolicTransversal,
  DoubleParabolicTransversalOps, DoubleParabolicTransversal,
  PDTransversalOps, PDTransversal, XJKLOps, XJKL, IsXJKL );

AUTO( ReadPkg( "zigzag", "lib", "walker" ),
  BreadthFirst, PreOrder, NrPreOrder, PreOrderProperty,
  NrPreOrderProperty, PostOrder, PostOrderProperty,
  NrPostOrderProperty, BinomialTreeOps, BinomialTree );

AUTO( ReadPkg( "zigzag", "lib", "zigzag" ),
  DescentAlgebraOps, DescentAlgebra, IsDescentAlgebra,
  CharacterDescentElt, SlowFoundation, SlowI, SlowCombine,
  MaximalAJKL1, MaximalAJKL2, MaximalAJKL, MatCompressedAJKL,
  ProductCompressedAJKL, RightRegularX, LeftRegularX, LeftRegularY,
  LeftRegularZ, LeftRegularE, DiagonalMat,
  SizesDescentConjugacyClasses, ECharacters, CCharacters,
  WhatCharacters, PrimitiveIdempotents, CartanMatDescent, HomDescent,
  RadicalDescent, RadicalSeriesDescent, MatsRadsDescent,
  ProjectiveModule, LaTeXProjectiveModule, MatDescentVec,
  MatQuiverSym, MajorIndex, RanMatDescent, SizMatDescent,
  LisMatDescent, ClosLis, OpenLis, ClosLisRank, OpenLisRank, Lat,
  RightIdeal, LeftIdeal, RightPIE, SetComposition, IsNonZero );

# print welcome message.
if BANNER then
    Print("ZigZag Version ", ZIGZAG.Version, " (", ZIGZAG.Date, ").\n");
fi;
