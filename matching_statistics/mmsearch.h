
#ifndef MM_SEARCH_H
#define MM_SEARCH_H

#include <cstdint>

using data_type = uint8_t;
using filelength_type = uint64_t;

void lzInitialize(data_type *ax, unsigned int *sa, unsigned int an, bool isMismatchingSymbolNeeded);

//returns the length of the RLZ parsing of sx relative to ax
int lzFactorize(char *fileToParse, int seqno, char* outputfilename, bool verbose);

#endif
