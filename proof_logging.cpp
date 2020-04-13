#include "proof_logging.h"

void proof_level_set(int level, std::ostream & proof_stream)
{
    proof_stream << "# " << level << std::endl;
}

void proof_level_wipe(int level, std::ostream & proof_stream)
{
    proof_stream << "w " << level << std::endl;
}


