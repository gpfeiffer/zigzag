#############################################################################
##
#A  init.g                        G�tz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This is the init file of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a
##  GAP package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: init.g,v 1.4 2006/05/30 09:23:54 goetz Exp $
##
AUTO( ReadPkg( "zigzag", "lib", "methods" ),
      Call,
      ApplyMethod );

AUTO( ReadPkg( "zigzag", "lib", "iterator" ),
      IteratorSet,
      IteratorRange,
      Iterator );

AUTO( ReadPkg( "zigzag", "lib", "shapes" ),
      ShapeOps,
      Shape,
      IsShape,
      Shapes,
      SubsetsShapes,
      ComplementsShapes,
      CollapsedIncMatShapes,
      CollapsedFusMatShapes,
      XCharacters,
      ParabolicTom,
      YCharacters,
      ZCharacters,
      InvolutionShapes,
      Involutions );

AUTO( ReadPkg( "zigzag", "lib", "arrows"),
      HeadArrow,
      TailArrow,
      OnArrows,
      DeltaArrow,
      ArrowClassOps,
      ArrowClass,
      IsArrowClass,
      ArrowClasses );

AUTO( ReadPkg( "zigzag", "lib", "subsets.g" ),
      PrefixesOps,
      Prefixes,
      IsPrefixes,
      WeakIntervalOps,
      WeakInterval,
      IsWeakInterval,
      ParabolicTransversalOps,
      ParabolicTransversal,
      IsParabolicTransversal,
      DescentClassOps,
      DescentClass,
      IsDescentClass,
      LeftParabolicTransversalOps,
      LeftParabolicTransversal,
      IsLeftParabolicTransversal,
      DoubleParabolicTransversalOps,
      DoubleParabolicTransversal,
      IsDoubleParabolicTransversal,
      XJKLOps,
      XJKL,
      IsXJL );

AUTO( ReadPkg( "zigzag", "lib", "zigzag.g" ),
      DescentAlgebraOps,
      DescentAlgebra,
      IsDescentAlgebra,
      CharacterDescentElt,
      MaximalAJKL, 
      MatCompressedAJKL, 
      ProductCompressedAJKL,
      RightRegularX,
      LeftRegularX,
      LeftRegularY,
      LeftRegularZ,
      LeftRegularE,
      SizesDescentConjugacyClasses,
      ECharacters,
      CCharacters,
      PrimitiveIdempotents,
      CartanMatDescent,
      RightPIE,
      SetComposition );

