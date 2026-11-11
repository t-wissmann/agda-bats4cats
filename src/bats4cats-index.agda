
-- (Finitely) accessible categories:
import Batteries.Object.Presentable
import Batteries.Category.Accessible
import Batteries.Category.Accessible.Finitely

-- Example: Setoids:
import Batteries.Category.Accessible.Instance.Setoids
import Batteries.Diagram.Colimit.Instance.FinCoequalizer
import Batteries.Diagram.Colimit.Setoids-Choice
import Batteries.Diagram.Colimit.Setoids-Colimit

-- Factorization systems:
import Batteries.Morphism.FactorizationSystem
import Batteries.Morphism.FactorizationSystem.Duality
import Batteries.Morphism.FactorizationSystem.Instance.Setoids
import Batteries.Morphism.FactorizationSystem.Properties

import Batteries.Morphism.Lifts-Patched
import Batteries.Morphism.Lifts-Patched.Properties

import Helper-Definitions
