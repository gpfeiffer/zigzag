#############################################################################
##
#A  init.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This is the init file of the ZigZag package.
##

#############################################################################
ZIGZAG:= rec();
ZIGZAG.Version:= "0.78";
ZIGZAG.Date:= "09-03-2011";

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
##  print welcome message.
##
if BANNER then
    Print("ZigZag Version ", ZIGZAG.Version, " (", ZIGZAG.Date, ").\n");
fi;

#############################################################################
##
#A  AUTO . . . . . . . . . . . . . . . . . . . . . . . . . . . .  auto reads.  
##
AUTO( ReadPkg( "zigzag", "lib", "forests" ), LeanTreeOps, LeanTree,
  IsLeanTree, IsSlanted, LeanTrees, SlantedLeanTrees, LeanForestOps,
  LeanForest, IsLeanForest, LeanForests, SlantedLeanForests,
  SortedSlantedLeanForests, CartanMatSortedSlantedLeanForests, TreeOps, Tree,
  IsTree, CompositionSubset, SubsetComposition, ForestOps, Forest, IsForest,
  ForestAlley, StandardFactorizationLyndon, StandardBracketingLyndon1,
  StandardBracketingLyndon, StandardBracketing, LyndonBasis, LyndonPaths,
  IsCompletelyReducibleStreet, NiceRelationsSym, DrawNiceRelation,
  IsCoreNiceRelation);

AUTO( ReadPkg( "zigzag", "lib", "blocks" ), VecBlVec, BlVecVec, MatBlMat,
  BlMatMat);

AUTO( ReadPkg( "zigzag", "lib", "skyline" ), FallingSequence, SkylineAOps,
  SkylineA, IsSkylineA, SkylineAPerm, SkylineAWord, SkylineBOps, SkylineB,
  IsSkylineB, SkylineBPerm, SkylineBWord, SkylineDOps, SkylineD, IsSkylineD,
  SkylineDPerm, SkylineDWord, MajorIndex);

AUTO( ReadPkg( "zigzag", "lib", "methods" ), Call, ApplyMethod, Map, Iverson,
  PartitionOps, Partition);

AUTO( ReadPkg( "zigzag", "lib", "subsets" ), SetComposition, IsLeftDescent,
  IsRightDescent, LongestElement, ConnectedComponent, ConnectedComponents,
  PrefixesOps, Prefixes, IsPrefixes, WeakIntervalOps, WeakInterval,
  IsWeakInterval, ParabolicTransversalOps, ParabolicTransversal,
  IsParabolicTransversal, ParabolicCoordinates, DescentClassOps, DescentClass,
  IsDescentClass, DescentClasses, SizesDescentConjugacyClasses,
  LeftParabolicTransversalOps, LeftParabolicTransversal,
  IsLeftParabolicTransversal, DoubleParabolicTransversalOps,
  DoubleParabolicTransversal, IsDoubleParabolicTransversal, XJKLOps, XJKL,
  IsXJKL);

AUTO( ReadPkg( "zigzag", "lib", "descent" ), DescentAlgebraOps,
  DescentAlgebra, IsDescentAlgebra, DescentEltOps, DescentElt, IsDescentElt,
  CharacterDescentElt, MaximalAJKL, MatCompressedAJKL, ProductCompressedAJKL,
  RightRegularX, LeftRegularX, LeftRegularY, LeftRegularZ, LeftRegularE,
  SymmetricMatrix, MatQuiverSym, LyndonFactorisation, CartanMatrixA,
  QCartanMatrixA, CartanMatrixB, QuiverRelations0, QuiverRelations1,
  QuiverRelations, SyzygiesQuiver, ProjectiveCover, ProjectiveResolutions,
  DescentQuiver, BasisProjectiveQuiver, NextProjectiveCover,
  ProjectiveResolution, RelationsDescentQuiver, DisplayQuiver0,
  DisplayQuiver1, DisplayQuiver, DimensionsMatrix0, DimensionsMatrix1,
  DimensionsMatrix, CartanMatQuiver0, CartanMatQuiver1, CartanMatQuiver,
  QCartanMatQuiver0, QCartanMatQuiver1, QCartanMatQuiver, LaTeXMatNames,
  KernelList, LaTeXQCartan, BlocksCartan, MatNrStreetsQuiver,
  QMatNrStreetsQuiver, MatNrPathsQuiver, QMatNrPathsQuiver,
  RedundantRelations);

AUTO( ReadPkg( "zigzag", "lib", "walker" ), BreadthFirst,
  IteratorBreadthFirst, PreOrderNC, PreOrder, NrPreOrderNC, NrPreOrder,
  IteratorPreOrder, PreOrderPropertyNC, PreOrderProperty,
  NrPreOrderPropertyNC, NrPreOrderProperty, PostOrderNC, PostOrder,
  PostOrderPropertyNC, PostOrderProperty, NrPostOrderPropertyNC,
  NrPostOrderProperty, BinomialTreeOps, BinomialTree, AlgorithmM,
  ProductsAlgorithmM, AlgorithmH, ProductsAlgorithmH, ExactPackings, FunCon,
  RestrictCon1, RestrictCon2);

AUTO( ReadPkg( "zigzag", "lib", "quiver" ), QuiverEltOps, QuiverElt,
  IsQuiverElt, QuiverOps, Quiver, IsQuiver);

AUTO( ReadPkg( "zigzag", "lib", "streets" ), StreetOps, Street, IsStreet,
  Streets, NrStreets, ProductStreetMatrices, ProductStreetMatrixList,
  SumStreetMatrices, ProductStreets, BasicStreets, BasicStreetsNonZero,
  PathsStreets, PathsStreets1, CartanMatStreets, QuiverMatStreets,
  CartanMatSlantedStreets0, SlantedStreets, CartanMatSlantedStreets,
  QuiverMatSlantedStreets, StreetAlgebraEltOps, StreetAlgebraElt,
  IsStreetAlgebraElt);

AUTO( ReadPkg( "zigzag", "lib", "faces" ), FaceOps, Face, IsFace, Faces,
  ProductLSigns, ProductRSigns, OnFaces, KernelSupportMap, FaceEltOps,
  FaceElt, IsFaceElt, ImageSupportMap, IncidenceIntersectionLattice,
  onReflectionSubgroups, PrimitiveIdempotentsFaceElts, NilpotentFaceElts,
  ProdMat);

AUTO( ReadPkg( "zigzag", "lib", "classes" ), CyclicShiftsOps, CyclicShifts,
  IsCyclicShifts, MinimalLengthConjugate, MaximalLengthConjugate,
  CentralizerComplementMinimal, CentralizerComplement, IsNonCompliant,
  CuspidalClasses, CyclicShiftClasses);

AUTO( ReadPkg( "zigzag", "lib", "iterator" ), IteratorList, IteratorEmpty,
  Iterator, IteratorRange, MPartitionsOps, MPartitions, NrMPartitions,
  PartitionsIntOps, PartitionsInt);

AUTO( ReadPkg( "zigzag", "lib", "alleys" ), ProductAlleys, ProductAlleyList,
  FactorsAlley, OnAlleys, StabilizerAlley, NrAlleys, LengthAlley, SourceAlley,
  TargetAlley, SubsetsAlley, PrefixAlley, SuffixAlley, ActionAlley,
  DeltaAlley, BigMatrixAlley, ReversedAlley, LittleDeltaBarAlley,
  ReducedWordAlley, ColoursAlley, AlleyAlgebraOps, AlleyAlgebra,
  IsAlleyAlgebra);

AUTO( ReadPkg( "zigzag", "lib", "groupoid" ), GroupoidOps, Groupoid,
  IsGroupoid, GroupoidEltOps, GroupoidElt, IsGroupoidElt);

AUTO( ReadPkg( "zigzag", "lib", "shapes" ), ShapeOps, Shape, IsShape,
  NormalizerComplement, IsBulkyParabolic, BulkyShapes, ShapesRank, Shapes,
  SubsetsShapes, ComplementsShapes, IncidenceMatShapes, XCharacters,
  ParabolicTom, YCharacters, ZCharacters, InvolutionShapes, Involutions,
  SpecialInvolutions, OrlikSolomonCharacter, NamesShapes, LabelsShapes,
  PathsShapes, IncMatShapes, QIncMatShapes, FusMatShapes, QFusMatShapes);

AUTO( ReadPkg( "zigzag", "lib", "category" ), CategoryOps, Category,
  IsCategory, CategoryEltOps, CategoryElt, IsCategoryElt);

AUTO( ReadPkg( "zigzag", "lib", "characte" ), RegularCharacter,
  TrivialCharacter, SignCharacter, GeneratorsAbelianGroup,
  LinearCharactersAbelianGroup, LinearCharacters, ECharacters);

