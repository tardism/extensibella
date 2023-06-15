grammar extensibella:toAbella:abstractSyntax;



--Name for the theorem for a relation from Ext_Ind
function extIndThmName
QName ::= rel::QName
{
  return addQNameBase(basicQName(rel.sub.moduleName),
                      "$extInd_" ++ rel.shortName);
}

--Name of accumulator relation for strong induction on ints
global intStrongInductionRel::QName = toQName("acc");
