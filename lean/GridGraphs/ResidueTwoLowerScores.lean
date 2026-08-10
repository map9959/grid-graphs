import GridGraphs.FiniteDiagonalConstructions

/-!
# Finite residue-two lower-score transitions

These are transitions between the scores of the explicit finite constructions.
In particular, the predecessor on the left is the displayed formula score, not
the previous value of `maxPreserved`.  No equality for the maximum at side
length fourteen is assumed.
-/

namespace GridGraphs

/-- The formula score at five, followed by the construction gain to eight. -/
theorem residueTwo_constructionScore_five_to_eight :
    (3 * 1 ^ 2 + 7 * 1 + 1) + 2 * 8 ≤ maxPreserved 8 8 := by
  change 27 ≤ maxPreserved 8 8
  exact twentySeven_le_maxPreserved_eight_eight

/-- The formula score at eight, followed by the construction gain to eleven. -/
theorem residueTwo_constructionScore_eight_to_eleven :
    (3 * 2 ^ 2 + 7 * 2 + 1) + 2 * 11 ≤ maxPreserved 11 11 := by
  change 49 ≤ maxPreserved 11 11
  exact fortyNine_le_maxPreserved_eleven_eleven

/-- The formula score at eleven, followed by the construction gain to fourteen. -/
theorem residueTwo_constructionScore_eleven_to_fourteen :
    (3 * 3 ^ 2 + 7 * 3 + 1) + 2 * 14 ≤ maxPreserved 14 14 := by
  change 77 ≤ maxPreserved 14 14
  exact seventySeven_le_maxPreserved_fourteen_fourteen

/-- The exceptional gain to seventeen is added to the formula score at
fourteen, not to the (not presently known to be equal) previous maximum. -/
theorem residueTwo_constructionScore_fourteen_to_seventeen :
    (3 * 4 ^ 2 + 7 * 4 + 1) + (2 * 17 - 1) ≤
      maxPreserved 17 17 := by
  change 110 ≤ maxPreserved 17 17
  exact oneHundredTen_le_maxPreserved_seventeen_seventeen

/-- The stable formula score at seventeen, followed by the full gain to twenty. -/
theorem residueTwo_constructionScore_seventeen_to_twenty :
    (3 * 5 ^ 2 + 7 * 5) + 2 * 20 ≤ maxPreserved 20 20 := by
  change 150 ≤ maxPreserved 20 20
  exact oneHundredFifty_le_maxPreserved_twenty_twenty

/-- The explicit twenty-by-twenty construction attains the stable residue-two
formula score. -/
theorem residueTwo_stable_formulaScore_twenty :
    3 * 6 ^ 2 + 7 * 6 ≤ maxPreserved 20 20 := by
  change 150 ≤ maxPreserved 20 20
  exact oneHundredFifty_le_maxPreserved_twenty_twenty

end GridGraphs
