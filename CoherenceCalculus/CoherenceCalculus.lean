-- Root module for the rebuilt proof chain.
--
-- The active library follows the new foundation chain only. Archived spine and
-- monolithic modules stay on disk as reference, but are not part of the active
-- root build unless they are re-derived cleanly above this base.
import CoherenceCalculus.Foundation
