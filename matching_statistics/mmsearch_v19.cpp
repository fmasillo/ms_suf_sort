#include <algorithm>
#include <chrono>
#include <ctime>
#include <fstream>
#include <iostream>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string.h>
#include <cstdlib>
#include <stack>

#include "mmsearch.h"
#include "rmq_tree.h"
#include "utils.h"
#include "match.h"
#include "predecessor.h"
#include "qsufsort.c"
#include "gsa-is/gsacak.c"
//#include "libdivsufsort/build/include/divsufsort.h"

#define likely(x)       __builtin_expect((x),1)

void computeLZFactorAt(filelength_type i, filelength_type *pos, filelength_type *len, int64_t &leftB, int64_t &rightB, int64_t &match, bool &isSmaller, unsigned char &mismatchingSymbol);
inline int64_t binarySearchLB(int64_t lo, int64_t hi, filelength_type offset, data_type c);
inline int64_t binarySearchRB(int64_t lo, int64_t hi, filelength_type offset, data_type c);

//static data_type *_x;
uint16_t sizeChars = 256;
std::string _x;
data_type *_BWT;
unsigned int *_SA;
uint32_t *_ISA;
uint32_t *_LCP;
rmq_tree *_rmq;
uint32_t _n;
data_type *_sx;
filelength_type _sn;
bool _isMismatchingSymbolNeeded;
std::vector<uint32_t> docBoundaries;
std::vector<uint32_t> headBoundaries;
predecessor2 pHeads;
uint32_t *C;
std::vector<uint32_t *> occ;
uint32_t nBlocks;
uint8_t *remapChr;
PsvNsv *pnsvDS;
const uint32_t shiftSize = 7;

uint64_t tiesCounter = 0;

uint64_t _maxLCP = 0;
uint64_t _numberOfShortFactors = 0;
uint64_t _numberOfSingleMatches = 0;

int renormalizations = 0;

uint64_t maxFactorLength = 0;
int lenZeroFactors = 0;

bool verbose;
uint64_t maxCounter = 0;
uint64_t denCounter = 0;
uint64_t sumCounter = 0;
uint64_t diffLenCounter = 0;
uint64_t finalSuffCounter = 0;

uint64_t diffSufPos;
uint64_t diffSufLen;
uint64_t diffSufHeads;

//std::vector<std::pair<uint32_t,uint32_t> > phrases;
std::vector<Match> phrases;
std::vector<MatchSA> headsSA;


//LCP array construction method of J. Kärkkäinen, G. Manzini, and S. J. Puglisi, CPM 2009
void constructLCP(std::string t, int32_t n, uint32_t *sa, uint32_t *lcp, uint32_t *temp) {
//void constructLCP(unsigned char *t, int32_t n, uint32_t *sa, uint32_t *lcp, uint32_t *temp) {
   fprintf(stderr,"\tComputing LCP...\n");
   int32_t *phi = (int32_t *)lcp, *plcp = (int32_t *)temp, l = 0;
   for (int32_t i = 1; i < n; ++i)
     phi[sa[i]] = sa[i-1];
   phi[sa[0]] = -1;
   for (int32_t i = 0; i < n; ++i) {
     int32_t j = phi[i];
     if (j == -1) { plcp[i] = 0; continue; }
     else {
       while (i + l < n && j + l < n && t[i + l] == t[j + l]) ++l;
       plcp[i] = l;
       l = std::max(l - 1, 0);
     }
   }
   for (int32_t i = 0; i < n; ++i)
     lcp[i] = plcp[sa[i]];
}

void constructISA(uint32_t *sa, uint32_t *isa, uint32_t n){
   fprintf(stderr,"\tComputing ISA...\n");
   for(uint32_t i=0; i<n; i++){
      isa[sa[i]] = i;
   }
}

void constructPSVNSV(uint32_t *lcp, PsvNsv *psvnsv, uint32_t n){
   std::stack<std::pair<uint32_t, uint32_t>> s;
   s.push(std::pair<uint32_t, uint32_t>(0, -1));
   psvnsv[0].psv = -1;
   for(uint32_t i = 1; i < n; i++){
      //std::cerr << "i: " << i << "\n";
      while(lcp[i] < s.top().second+(s.top().second == -1)){
         psvnsv[s.top().first].nsv = i;
         s.pop();
      }
      if(lcp[i] > s.top().second){
         psvnsv[i].psv = s.top().first;
      }
      else{
         psvnsv[i].psv = psvnsv[s.top().first].psv;
      }
      s.push(std::pair<uint32_t,uint32_t>(i, lcp[i]));
   }
   // for(uint32_t i = 0; i < n; i++){
   //    std::cerr << i << " LCP[i]: " << lcp[i] << " " << psvnsv[i].psv << ", " << psvnsv[i].nsv << "\n";
   // }
}

std::pair<int,int> adjustInterval(int lo, int hi, int offset) {
  int psv = _rmq->psv(lo,offset);
  if(psv == -1){
    psv = 0;
  }else{
    //psv++;
  }
  int nsv = _rmq->nsv(hi+1,offset);
  if(nsv == -1){
    nsv = _n-1;
  }else{
    nsv--;
  }
  return std::make_pair(psv,nsv);
}

std::pair<int,int> contractLeft(int lo, int hi, int offset){
   uint32_t suflo = _SA[lo];
   uint32_t sufhi = _SA[hi];
   if(suflo == _n-1 || sufhi == _n-1){ //if true we must be at depth 1
      return std::make_pair(0,_n-1); //root
   }
   uint32_t tmplo = _ISA[suflo+1]; 
   uint32_t tmphi = _ISA[sufhi+1];
   return adjustInterval(tmplo, tmphi, offset);
}

uint32_t findOcc(const data_type c, const uint32_t i){
   //if(i == 0 | i == -1) return 0;
   uint32_t result = 0;
   __builtin_prefetch(&_BWT[(i >> shiftSize) << shiftSize]);
   //__builtin_prefetch(&_BWT[(i >> shiftSize) << shiftSize + 1]);
   if(i > 127){
      //if(verbose) std::cerr << "i was " << i << "\n";
      result += occ[(i >> shiftSize) - 1][c];
   }
   //if(verbose) std::cerr << "start index of block " << (i / 512) * 512 << " " << (i / 512) * 512 - 1 << "\n";
   for(uint32_t j = ((i >> shiftSize) << shiftSize); j < i+1; j++){
      //if(verbose) std::cerr << "i in while " << i << "\n";
      //if(_BWT[j] == c) result++;
      result += (_BWT[j] == c);
      //i--;
   }
   //if(verbose) std::cerr << "i in while " << i << "\n";
   //if(_BWT[i] == c) result++;
   return result;
}  

const inline void parentInterval(uint32_t &i, uint32_t &j, uint32_t &len){
   // if(i == 0 & j == _n-1){
   //    len = 0;
   //    return;
   // }
   //if(verbose) std::cerr << "i: " << i << " j+1: " << j+1 << "\n";
   //__builtin_prefetch(&pnsvDS[i]);
   //__builtin_prefetch(&pnsvDS[j+1]);
   if(_LCP[i] < _LCP[j+1]){
      bool jFound = false;
      len = _LCP[j+1];
      //if(verbose) std::cerr << "LCP[i] < LCP[j+1]: " << _LCP[i] << " < " << _LCP[j+1] << "\n";
      // if(j!=0) for(uint32_t idx = j; idx > j-50 & idx >= 0; idx--){
      //    if(_LCP[idx] < len){
      //       i = idx;
      //       iFound = true;
      //       break;
      //    }
      // }
      // if(!iFound){
      //    i = pnsvDS[j+1].psv;
      //    i += (i == -1);
      // }
      // i = _rmq->psv(tmpj+1, len);
      //if(verbose) std::cerr << "new i: " << i << "\n";
      //if(i == -1) i = 0;
      if(j+1<_n-1) for(uint32_t idx = j+2; idx < j+129 & idx < _n; idx++){
         if(_LCP[idx] < len){
            j = idx-1;
            jFound = true;
            break;
         }
      }
      if(!jFound){
         j = pnsvDS[j+1].nsv;
         // j = _rmq->nsv(tmpi, len);
         if(j == -1){
            j = _n-1;
         }else{
            j--;
         }
      }
      //if(verbose) std::cerr << "new j: " << j << "\n";
      //if(verbose) std::cerr << "Ended search for parent interval\n";
   }
   else if(_LCP[i] > _LCP[j+1]){
      bool iFound = false;
      len = _LCP[i];
      //uint32_t tmpi = i;
      //std::cerr << "LCP[i] >= LCP[j+1]: " << _LCP[i] << " >= " << _LCP[j+1] << "\n";
      if(i!=0) for(uint32_t idx = i-1; idx > i-128 & idx >= 0; idx--){
         if(_LCP[idx] < len){
            i = idx;
            iFound = true;
            break;
         }
      }
      if(!iFound){
         i = pnsvDS[i].psv;
         i += (i == -1);
      }
      // i = _rmq->psv(tmpi, len);
      //std::cerr << "new i: " << i << "\n";
      //j = pnsvDS[tmpi].nsv;
      // j = _rmq->nsv(tmpi, len);
      // if(j == -1){
      //    j = _n-1;
      // }else{
      //    j--;
      // }
      //std::cerr << "new j+1: " << j+1 << "\n";
      //if(verbose) std::cerr << "Ended search for parent interval\n";
   }
   else{
      bool iFound = false, jFound = false;
      len = _LCP[i];
      if(i<_n-1)for(uint32_t idx = i+1; idx < i+128 & idx < _n; idx++){
         if(_LCP[idx] < len){
            j = idx-1;
            jFound = true;
            break;
         }
      }
      if(!jFound){
         j = pnsvDS[i].nsv;
         // j = _rmq->nsv(tmpi, len);
         if(j == -1){
            j = _n-1;
         }else{
            j--;
         }
      }
      //if(verbose) std::cerr << "LCP[i] >= LCP[j+1]: " << _LCP[i] << " >= " << _LCP[j+1] << "\n";
      if(i!=0) for(uint32_t idx = i-1; idx > i-128 & idx >= 0; idx--){
         if(_LCP[idx] < len){
            i = idx;
            iFound = true;
            break;
         }
      }
      if(!iFound){
         i = pnsvDS[i].psv;
         i += (i == -1);
      }
      // i = _rmq->psv(tmpi, len);
      //if(verbose) std::cerr << "new i: " << i << "\n";
      //if(i == -1) i = 0;
      
      //if(verbose) std::cerr << "new j+1: " << j+1 << "\n";
   }
}


inline uint32_t radixSortSmaller(const std::vector<MatchSA>::iterator a, const uint32_t start, const uint32_t end, uint32_t *buckets, uint32_t *startIndex){
   std::vector<MatchSA> result; 
   result.resize(end-start); 
   //uint32_t *buckets = new uint32_t[2]();
   //uint32_t *startIndex = new uint32_t[2]();
   uint32_t key = 0;
   
   for(std::vector<MatchSA>::iterator it = a+start; it < a+end; ++it) {
      ++buckets[it->smaller];
   }
   startIndex[0] = 0;
   startIndex[1] = buckets[0];
   for(std::vector<MatchSA>::iterator it = a+end-1; it >= a+start; --it){
      key = it->smaller;
      result[startIndex[key] + --buckets[key]] = *it;
   }
   std::copy(result.begin(), result.end(), a+start);
   key = startIndex[1];
   //delete[] buckets;
   //delete[] startIndex;
   return key;
}

inline void radixSortLen(const std::vector<MatchSA>::iterator a, const uint32_t start, const uint32_t end, uint32_t *buckets, uint32_t *startIndex){
   const uint32_t INT_BIT_SIZE = sizeof(uint32_t)<<3; int RADIX = 0x100, MASK = RADIX-1, MASK_BIT_LENGTH = 8;
   std::vector<MatchSA> result;
   result.resize(end-start);  
   //uint32_t *buckets = new uint32_t[RADIX](); 
   //uint32_t *startIndex = new uint32_t[RADIX]();
   uint32_t flag = 0, key = 0;
   for(flag; flag < 32; flag+=8){
      for(std::vector<MatchSA>::iterator it = a+start; it < a+end; ++it) {
         key = (it->len & (MASK << flag)) >> flag;
         ++buckets[key];
      }
      startIndex[0] = 0;
      for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j - 1];
      for(std::vector<MatchSA>::iterator it = a+end-1; it >= a+start; --it){
         key = (it->len & (MASK << flag)) >> flag;
         result[startIndex[key] + --buckets[key]] = *it;
      }
      std::copy(result.begin(), result.end(), a+start);
      //flag += MASK_BIT_LENGTH;
   }
   //std::reverse(a.begin()+start, a.begin()+end);
   //delete[] buckets;
   //delete[] startIndex;
}

inline void radixSortLenDecr(const std::vector<MatchSA>::iterator a, const uint32_t start, const uint32_t end, uint32_t *buckets, uint32_t *startIndex){
   const uint32_t INT_BIT_SIZE = sizeof(uint32_t)<<3; int RADIX = 0x100, MASK = RADIX-1, MASK_BIT_LENGTH = 8;
   std::vector<MatchSA> result;
   result.resize(end-start);  
   //uint32_t *buckets = new uint32_t[RADIX](); 
   //uint32_t *startIndex = new uint32_t[RADIX]();
   uint32_t flag = 0, key = 0;
   for(flag; flag < 32; flag+=8){
      for(std::vector<MatchSA>::iterator it = a+start; it < a+end; ++it) {
         key = (it->len & (MASK << flag)) >> flag;
         ++buckets[RADIX - key - 1];
      }
      startIndex[0] = 0;
      for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j-1];
      for(std::vector<MatchSA>::iterator it = a+end-1; it >= a+start; --it){
         key = (it->len & (MASK << flag)) >> flag;
         result[startIndex[RADIX - key - 1] + --buckets[RADIX - key - 1]] = *it;
      }
      std::copy(result.begin(), result.end(), a+start);
      //flag += MASK_BIT_LENGTH;
   }
   //delete[] buckets;
   //delete[] startIndex;
}

inline void radixSortChar(const std::vector<MatchSA>::iterator a, const uint32_t start, const uint32_t end, uint32_t *buckets, uint32_t *startIndex){
   const uint32_t INT_BIT_SIZE = sizeof(data_type)<<3; int RADIX = 0x100, MASK = RADIX-1, MASK_BIT_LENGTH = 8;
   std::vector<MatchSA> result; 
   result.resize(end-start); 
   uint32_t flag = 0, key = 0;
    
   for(std::vector<MatchSA>::iterator it = a+start; it < a+end; ++it) {
      key = (it->next & (MASK << flag)) >> flag;
      ++buckets[key];
   }
   startIndex[0] = 0;
   for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j - 1];
   for(std::vector<MatchSA>::iterator it = a+end-1; it >= a+start; --it){
      key = (it->next & (MASK << flag)) >> flag;
      result[startIndex[key] + --buckets[key]] = *it;
   }
   std::copy(result.begin(), result.end(), a+start);
   //delete[] buckets;
   //delete[] startIndex;
}

void radixSortPos(const std::vector<MatchSA>::iterator a, const uint32_t start, const uint32_t end){
   const uint32_t INT_BIT_SIZE = sizeof(uint32_t)<<3; int RADIX = 0x100, MASK = RADIX-1, MASK_BIT_LENGTH = 8;
   std::vector<MatchSA> result;
   result.resize(end-start);  
   uint32_t *buckets = new uint32_t[RADIX](); 
   uint32_t *startIndex = new uint32_t[RADIX]();
   uint32_t flag = 0, key = 0;
   for(flag; flag < 32; flag+=8){
      for(std::vector<MatchSA>::iterator it = a+start; it < a+end; ++it) {
         key = (it->pos & (MASK << flag)) >> flag;
         ++buckets[key];
      }
      startIndex[0] = 0;
      for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j - 1];
      for(std::vector<MatchSA>::iterator it = a+end-1; it >= a+start; --it){
         key = (it->pos & (MASK << flag)) >> flag;
         result[startIndex[key] + --buckets[key]] = *it;
      }
      std::copy(result.begin(), result.end(), a+start);
      flag += MASK_BIT_LENGTH;
   }
   //std::reverse(a.begin()+start, a.begin()+end);
   delete[] buckets;
   delete[] startIndex;
}

bool compareMatchSA(const MatchSA &a, const MatchSA &b){
   if(a.smaller == 0 & b.smaller == 0){
      return (a.next < b.next)*(a.len == b.len) + (a.len < b.len)*(a.len != b.len);
   }
   else if(a.smaller == 1 & b.smaller == 1){
      return (a.next < b.next)*(a.len == b.len) + (a.len > b.len)*(a.len != b.len);
   }
   return a.smaller < b.smaller;
}

bool compareSuf(const SufSStar &a, const SufSStar &b){
   //finalSuffCounter++;
   MatchSA headA = headsSA[a.head];
   MatchSA headB = headsSA[b.head];
   if(headA.len - a.diffLen != headB.len - b.diffLen){
      //diffSufLen++;
      return headA.smaller*((headA.len - a.diffLen) < (headB.len - b.diffLen)) + 
            !headB.smaller*((headA.len - a.diffLen) > (headB.len - b.diffLen));
   }
   else{
      return (headA.pos != headB.pos)*(headA.pos < headB.pos) + (headA.pos == headB.pos)*(headA.start<headB.start);
   }
   // return headA.smaller*((headA.len - a.diffLen) < (headB.len - b.diffLen)) + 
   //       !headB.smaller*((headA.len - a.diffLen) > (headB.len - b.diffLen)) +
   //        ((headA.pos != headB.pos)*(headA.pos < headB.pos) + 
   //        (headA.pos == headB.pos)*(headA.start<headB.start))*((headA.len - a.diffLen) == (headB.len - b.diffLen));
}

uint64_t checkHeadsSA(std::vector<MatchSA> &GSA, uint64_t n){
   uint64_t err = 0;
   for(size_t i = 0; i < n; i++){
      if(verbose) std::cerr << "i=" << i << ": " << phrases[GSA[i].start].start << " " << GSA[i].len << " " << "\n";//MSGSA[i].head <<"\n";
   //  if(GSA[i].len == 0 || GSA[i-1].len == 0){
   //     std::cerr << "There was an empty entry\n";
   //     continue;
   //  }
      data_type *_slice_sx = _sx + phrases[GSA[i].start].start + docBoundaries[GSA[i].len - 1];
      data_type *_slice_prev;
      uint32_t maxIdx;
      if(i > 0){
      _slice_prev = _sx + phrases[GSA[i-1].start].start + docBoundaries[GSA[i-1].len - 1];
      maxIdx = std::min(docBoundaries[GSA[i].len] - (phrases[GSA[i].start].start + docBoundaries[GSA[i].len - 1]), docBoundaries[GSA[i-1].len] - (phrases[GSA[i-1].start].start + docBoundaries[GSA[i-1].len - 1]));
      } 
      else{
         _slice_prev = (data_type *)"$";
         maxIdx = 1;
      }
      if(verbose) std::cerr << "suf_i-1 " << _slice_prev;
      if(verbose) std::cerr << "suf_i " << _slice_sx << "\n";
      
   if(memcmp(_slice_sx, _slice_prev, maxIdx) < 0){
      if(verbose) std::cerr << "PROBLEM with " << i-1 << " (" << phrases[GSA[i-1].start].start << "," << GSA[i-1].len << ") and " << i << " (" << phrases[GSA[i].start].start << "," << GSA[i].len << ")\n"; 
      err++;
   }
   }
   return err;
}

uint64_t checkGSA(std::vector<SufSStar> GSA, uint64_t n){
   uint64_t err = 0;
   for(size_t i = 0; i < n; i++){
      if(verbose) std::cerr << "i=" << i << ": " << GSA[i].idx << " " << GSA[i].doc << " " << "\n";//MSGSA[i].head <<"\n";
      if(GSA[i].doc == 0 || GSA[i-1].doc == 0){
         std::cerr << "There was an empty entry\n";
         continue;
      }
      data_type *_slice_sx = _sx + GSA[i].idx + docBoundaries[GSA[i].doc - 1];
      data_type *_slice_prev;
      uint32_t maxIdx;
      if(i > 0){
      _slice_prev = _sx + GSA[i-1].idx + docBoundaries[GSA[i-1].doc - 1];
      maxIdx = std::min(docBoundaries[GSA[i].doc] - (GSA[i].idx + docBoundaries[GSA[i].doc - 1]), docBoundaries[GSA[i-1].doc] - (GSA[i-1].idx + docBoundaries[GSA[i-1].doc - 1]));
      } 
      else{
         _slice_prev = (data_type *)"$";
         maxIdx = 1;
      }
      if(verbose) std::cerr << "suf_i-1 " << _slice_prev;
      if(verbose) std::cerr << "suf_i " << _slice_sx << "\n";
      
   if(memcmp(_slice_sx, _slice_prev, maxIdx) < 0){
      if(verbose) std::cerr << "PROBLEM with " << i-1 << " (" << GSA[i-1].idx << "," << GSA[i-1].doc << ") and " << i << " (" << GSA[i].idx << "," << GSA[i].doc << ")\n"; 
      err++;
   }
   }
   return err;
}

void lzInitialize(data_type *ax, unsigned int an, bool isMismatchingSymbolNeeded, char *refFileName, char *collFileName) {
   _x = std::string(reinterpret_cast<char const *>(ax), an);
   if((_x[_x.size()-1] == '\n') | (_x[_x.size()-1] == '\r')){
      _x.erase(_x.size()-1);
   }
   if(_x[_x.size()-1] == '$'){
      _x.erase(_x.size()-1);
   }
   FILE *infile = fopen(collFileName, "r");
   if(!infile){
      fprintf(stderr, "Error opening file of sequence (%s)\n", collFileName);
      exit(1);
   }
   filelength_type sn = 0;
   fseek(infile, 0L, SEEK_END);
   sn = ftello(infile) / sizeof(data_type);
   std::cerr << "sn: " << sn << '\n';
   fseek(infile, 0L, SEEK_SET);
   data_type *sx = new data_type[sn + 1];
   if(sn != fread(sx, sizeof(data_type), sn, infile)){
      fprintf(stderr, "Error reading %lu bytes from file %s\n", sn, collFileName);
      exit(1);
   }
   sx[sn] = 1; //I don't think there is any reason to do this
   fclose(infile);

   uint64_t *maxRunsReference = new uint64_t[sizeChars]();
   data_type c = '<';
   uint64_t runLen = 0;
   for(uint32_t i = 0; i < _x.size(); i++){
      if(_x[i] != c){
         if(runLen > maxRunsReference[c]){
            maxRunsReference[c] = runLen;
         }
         runLen = 1;
         c = _x[i];
         continue;
      }
      runLen++;
   }

   c = '<';
   runLen = 0;
   uint64_t *maxRunsCollection = new uint64_t[sizeChars]();
   for(uint64_t i = 0; i < sn; i++){
      if(sx[i] != c){
         if(runLen > maxRunsCollection[c]){
            maxRunsCollection[c] = runLen;
         }
         runLen = 1;
         c = sx[i];
         continue;
      }
      runLen++;
   }

   //std::string refAug(_x);
   std::vector<data_type> chrSeen;
   chrSeen.push_back('$');
   chrSeen.push_back('\n');
   for(uint16_t i = 0; i < sizeChars; i++){
      if(verbose) std::cerr << (char)i << " ref: " << maxRunsReference[i] << ", coll: " << maxRunsCollection[i] << "\n";
      if((maxRunsReference[i] == 0) & (maxRunsCollection[i] != 0) & (i != '%')){
         for(uint32_t x = 0; x < maxRunsCollection[i]; x++){
            _x += (char)i;
         }
         chrSeen.push_back(i);
      }
      else if((maxRunsReference[i] != 0) | (maxRunsCollection[i] != 0)){
         chrSeen.push_back(i);
      }
   }
   std::sort(chrSeen.begin(), chrSeen.end());
   remapChr = new uint8_t[sizeChars]();
   for(uint16_t newKey = 0; newKey < chrSeen.size(); newKey++){
      remapChr[chrSeen[newKey]] = newKey;
   }
   _x += '$';
   _x += '\n';
   docBoundaries.reserve(maxRunsCollection['%']);
   headBoundaries.reserve(maxRunsCollection['%']);
   //std::cerr << refAug << "\n";
   
   char refAugFileName[256];
   sprintf(refAugFileName, "%s.aug", refFileName);
   std::ofstream fout(refAugFileName, std::ios::out | std::ios::binary);
   fout.write(_x.c_str(), _x.size());
   fout.close();

   /* Allocate 5blocksize bytes of memory. */
   char saFileName[1024]; 
   sprintf(saFileName, "%s.sa", refAugFileName);
   char command[2048];
   sprintf(command, "libdivsufsort/build/examples/./mksary %s %s", refAugFileName, saFileName);
   system(command);

   fprintf(stderr, "About to read SA of ref\n");
   std::cerr << saFileName << '\n';
   infile = fopen(saFileName, "r");
   if (!infile) {
      fprintf(stderr, "Error opening suffix array of input file %s\n", saFileName);
      exit(1);
   }
   unsigned int san = 0;
   fseek(infile, 0, SEEK_END);
   san = ftell(infile) / sizeof(unsigned int);
   std::cerr << "san = " << san << '\n';
   fseek(infile, 0, SEEK_SET);
   unsigned int *sa = new unsigned int[san];
   if (san != fread(sa, sizeof(unsigned int), san, infile)) {
      fprintf(stderr, "Error reading sa from file\n");
      exit(1);
   }
   fclose(infile);
   
   //_x = refAug.c_str();
   //std::string().swap(refAug);
   _sx = sx;
   if(_sx[sn-1] != '%')
      _sn = sn - 1;
   else
      _sn = sn;
   std::cerr << "Last pos " << _sx + _sn - 1 << "\n";
   _n = _x.size();

   _SA = sa;
   _ISA = new uint32_t[_n];
   _LCP = new uint32_t[_n];
   constructLCP(_x,_n,_SA,_LCP,_ISA);
   std::cerr << "Computed LCP array\n";
   for(uint32_t i=0;i<_n;i++){
      if(_LCP[i] > _maxLCP & _x[_SA[i]] != 'N') _maxLCP = _LCP[i];
   }
   std::cerr << "_maxLCP = " << _maxLCP << '\n';
   constructISA(_SA,_ISA,_n);
   std::cerr << "Computed ISA array\n";
   std::cerr << "Computing PSV/NSV\n";
   pnsvDS = new PsvNsv[_n];
   constructPSVNSV(_LCP, pnsvDS, _n);
   std::cerr << "Computed PSV/NSV\n";
   //fprintf(stderr,"\tComputing RMQ...\n");
   //_rmq = new rmq_tree((int *)_LCP, _n, 7);
   _isMismatchingSymbolNeeded = isMismatchingSymbolNeeded;
   
   std::cerr << "Computing the BWT while remapping characters\n";
   _BWT = new data_type[_n];
   for(uint32_t i = 0; i < _n; i++){
      if(_SA[i] != 0) _BWT[i] = remapChr[_x[_SA[i]-1]];
      else _BWT[i] = remapChr[_x[_n-1]];
   }
   nBlocks = ceil((float)_n/128);
   std::cerr << "Number of chrSeen: " << chrSeen.size() << "\n";
   std::cerr << "Number of blocks: " << nBlocks << "\n";
   occ.resize(nBlocks);
   for(uint32_t i = 0; i < nBlocks; i++){
      occ[i] = new uint32_t[chrSeen.size()]();
   }
   for(uint32_t i = 0; i < _n; i++){
      occ[i >> shiftSize][_BWT[i]]++; 
   }
   uint32_t *cumulativeOcc = new uint32_t[chrSeen.size()]();;
   for(uint32_t i = 0; i < nBlocks; i++){
      //std::cerr << "block: " << i << "\n";
      for(uint16_t j = 0; j < chrSeen.size(); j++){
         cumulativeOcc[j] += occ[i][j];
         occ[i][j] = cumulativeOcc[j];
         //std::cerr << (data_type)chrSeen[j] << ": " << occ[i][j] << "\n";
      }
   }
   C = new uint32_t[chrSeen.size()];
   C[0] = 0;
   for(uint16_t i = 1; i < chrSeen.size(); i++){
      C[i] = C[i-1] + cumulativeOcc[i-1];
   }
   std::cerr << "Finished pre-processing\n";
   //exit(0);
   //TODO: preprocess SA and store intervals containing all suffixes with a given short prefix
}

int lzFactorize(char *fileToParse, int seqno, char* outputfilename, const bool v) {
   verbose = v;
   
   std::cerr << "File is in memory\n";
   auto t1 = std::chrono::high_resolution_clock::now();

   std::vector<filelength_type> starts;
   std::vector<uint32_t> sources;
   std::vector<uint32_t> lengths;
   std::vector<uint8_t> nextSymbols;

   std::vector<Match> matches;

   unsigned int numfactors = 0;

   unsigned int inc = 100000000;
   uint64_t mark = inc;

   //std::pair<uint32_t, uint32_t> *GSA = new std::pair<uint32_t, uint32_t>[_sn];

   std::cerr << "About to start main parsing loop...\n";

   int64_t leftB = 0;
   int64_t rightB = _n-1;
   int64_t match;
   bool isSmallerThanMatch;
   unsigned char mismatchingSymbol;
   int64_t prevPos = -2;
   int64_t lpfRuns = 0;
   uint32_t pos = 0, len = 0;
   docBoundaries.push_back(0);
   uint32_t ndoc = 1;
   uint32_t iCurrentDoc = 0;
   //uint32_t *bucketLengths = new uint32_t[_n]();
   uint32_t *bucketLengthsStar = new uint32_t[_n]();
   //uint32_t *bucketLengthsStar = new uint32_t[sizeChars]();
   uint32_t *bucketLengthStarChar = new uint32_t[sizeChars]();
   uint32_t *bucketLengthsHeads = new uint32_t[_n]();
   //uint32_t *bucketLengthsHeads = new uint32_t[sizeChars]();
   // if(verbose) for(size_t s = 0; s < _n; s++){
   //    std::cerr << s << "\t" << _SA[s] << "\t" << _x[_SA[s]];
   // }

   bool *typeArray = new bool[_sn];
   typeArray[_sn - 1] = 0;
   for(uint64_t i = _sn - 2; i < _sn; i--){
      if(_sx[i] < _sx[i+1]){
         typeArray[i] = 0;
      }
      else if(_sx[i] == _sx[i+1]){
         typeArray[i] = typeArray[i+1];
      }
      else{
         typeArray[i] = 1;
      }
   }
   headBoundaries.push_back(0);
   //uint64_t i = 0;
   uint64_t nStar = 0;
   uint64_t *charBkts = new uint64_t[sizeChars]();
   uint64_t maxValue = 0;
   int64_t i = _sn - 1;
   uint32_t left = 0, right = _n - 1, l = 0, r = _n - 1;
   uint64_t idxProcessed = 0;
   std::chrono::_V2::system_clock::time_point tB0, tB1, tI0, tI1;
   uint64_t sumTB = 0, sumTI = 0, maxLen = 0, sumLen = 0, nTB = 0, nTI = 0;
   while(i > -1){
      //std::cerr << i << "\n";
      //if(idxProcessed > 38740001) verbose = 1;
      if(idxProcessed > mark){
         fprintf(stderr,"i = %lu; lpfRuns = %ld\n",idxProcessed,lpfRuns);
         mark = mark + inc;
      }
      //if(verbose) std::cerr << "i: " << i << " " << _sx[i] << " left: " << left << " right: " << right << " len: " << len << "\n";
      charBkts[_sx[i]]++;
      if(_sx[i] != '%'){
         //if(verbose) std::cerr << "Starting backwardSearch\n";
         //tB0 = std::chrono::high_resolution_clock::now();
         //backwardSearch(remapChr[_sx[i]], left, right, l ,r);
         data_type c = remapChr[_sx[i]];
         l = (left < 2) ? C[c] : C[c] + findOcc(c, left-1);
         r = (right == 0 | right == -1) ? C[c] - 1 : C[c] + findOcc(c, right) - 1;
         //tB1 = std::chrono::high_resolution_clock::now();
         //sumTB += std::chrono::duration_cast<std::chrono::nanoseconds>(tB1 - tB0).count();
         //nTB++;
         //if(verbose) std::cerr << "backwardSearch finished. Left: " << l << " right: " << r << "\n";
         if(l <= r){
            //pos = left + findOcc(remapChr[_sx[i+len+1]], left);
            left = l;
            right = r;
            len++;
            //if(len > maxLen) maxLen = len;
            sumLen += len;
            if(left != prevPos-1){
               //phrases.push_back(Match(iCurrentDoc, pos, len, _sx[i+len]<_x[left+len]));
               //bucketLengthsHeads[_ISA[left]]++;
               lpfRuns++;
            }
            if(i>0){
               if((typeArray[i] == 0) & (typeArray[i-1] == 1)){
                  bucketLengthsStar[_ISA[left]]++;
                  //bucketLengthsStar[_ISA[pos]]++;
                  bucketLengthStarChar[_sx[i]]++;
                  nStar++;
               }
            }
            i--;
            idxProcessed++;
            // if(left > 128) __builtin_prefetch(&occ[(left-1) >> shiftSize - 1][remapChr[_sx[i]]]);
            // if(right > 127) __builtin_prefetch(&occ[(right) >> shiftSize - 1][remapChr[_sx[i]]]);
         }
         // else if(left == 0 & right == _n - 1){
         //    //phrases.push_back(Match(iCurrentDoc, pos, len, _sx[i+len]<_x[pos+len]));
         //    len = 0;
         //    //left = l;
         //    //right = r;
         //    i--;
         // }
         else{
            //if(verbose) std::cerr << "Going to find parent interval \n";
            //tI0 = std::chrono::high_resolution_clock::now();
            parentInterval(left, right, len);
            //tI1 = std::chrono::high_resolution_clock::now();
            //sumTI += std::chrono::duration_cast<std::chrono::nanoseconds>(tI1 - tI0).count();
            //nTI++;
            //if(verbose) std::cerr << "New interval: "  << " left: " << left << " right: " << right << " len: " << len << "\n";
         }
      }
      else{
         //if(verbose) std::cerr << "NEW DOC!!\n";
         left = 0, right = _n - 1;
         pos = _n - 1;
         len = 0;
         phrases.push_back(Match(iCurrentDoc, pos, len, 0));
         bucketLengthsHeads[_ISA[pos]]++;
         bucketLengthsStar[_ISA[pos]]++;
         bucketLengthStarChar['%']++;
         nStar++;
         i--;
         lpfRuns++;
         idxProcessed++;
      }
      prevPos = left;
   } 
   std::cerr << "max len " << maxLen << " meanLen " << (float)sumLen/_sn << "\n";
   std::cerr << "tBSum " << (float)sumTB/nTB << " nanosec, tIsum " << (float)sumTI/nTI << " nanosec\n";
   auto t2 = std::chrono::high_resolution_clock::now();
   uint64_t lzFactorizeTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to compute matching statistics: " << lzFactorizeTime << " milliseconds\n";

   exit(0);
   // while(i < _sn) {
   //    //std::cout << "i: " << i << "\n";
   //    if(i > mark){
   //       fprintf(stderr,"i = %lu; lpfRuns = %ld\n",i,lpfRuns);
   //       mark = mark + inc;
   //    }
   //    computeLZFactorAt(i, &pos, &len, leftB, rightB, match, isSmallerThanMatch, mismatchingSymbol);
   //    if(_sx[i] == '%'){
   //       pos = _n-1;
   //    }
   //    if((int64_t)pos != prevPos+1 || len == 0){
   //       phrases.push_back(Match(iCurrentDoc, pos, len, isSmallerThanMatch));
   //       bucketLengthsHeads[_ISA[pos]]++;
   //       lpfRuns++;
   //       //if(maxFactorLength < len){ maxFactorLength = len; }
   //       //if(len <= _maxLCP){ _numberOfShortFactors++; }
   //       numfactors++;
   //    }
   //    //bucketLengths[_ISA[pos]]++;
   //    charBkts[_sx[i]]++;
   //    prevPos = pos;
   //    if(i>0){
   //       if((typeArray[i] == 0) & (typeArray[i-1] == 1)){
   //          bucketLengthsStar[_ISA[pos]]++;
   //          //bucketLengthsStar[_ISA[pos]]++;
   //          bucketLengthStarChar[_sx[i]]++;
   //          nStar++;
   //       }
   //    }
      
   //    iCurrentDoc++;
   //    //len == 0 || 
   //    if(_sx[i] == '%'){ //new doc found
   //       pos = (((uint32_t)_sx[i]) | (1<<31)); 
   //       docBoundaries.push_back(iCurrentDoc + docBoundaries[ndoc-1]); 
   //       headBoundaries.push_back(phrases.size());
   //       if(maxValue < iCurrentDoc) maxValue = iCurrentDoc;
   //       iCurrentDoc = 0; 
   //       ndoc++;
   //    }
   //    if (len == 0){
   //       lenZeroFactors++;
   //       len++;
   //    }
   //    i++;
   //    if(len == 1 || pos == _n){
   //       //root
   //       leftB = 0;
   //       rightB = _n-1;
   //       len = 0;
   //    }else{
   //       //Contract left
   //       //Prepare for next position
   //       //std::cout << "Contracting left" << "\n";
   //       len--;
   //       if(leftB == rightB && len > _maxLCP){
   //          leftB = rightB = _ISA[_SA[leftB]+1];
   //          _numberOfSingleMatches++;
   //          //if(verbose) std::cerr << "No contractLeft\n";
   //       }else{
   //          std::pair<int,int> interval = contractLeft(leftB,rightB,len);
   //          leftB = interval.first;
   //          rightB = interval.second;
   //          //if(verbose) std::cerr << "Yes contractLeft" << leftB << "," << rightB << "\n";
   //       }
   //    }
   // }
   std::string().swap(_x);
   std::cerr << headBoundaries.size() << ", " << ndoc << "\n";
   std::cerr << "phrases.size() = " << phrases.size() << "\n";
   if(verbose) for(uint64_t i = 0; i < phrases.size(); i++) std::cerr << phrases[i].start << "," << phrases[i].pos << "," << phrases[i].len << '\n';
   pHeads = predecessor2(phrases, headBoundaries, ndoc, maxValue);
   //std::vector<uint32_t>().swap(headBoundaries);
   // pHeads = predecessor(phrases, headBoundaries, ndoc);
   // Match a = *(pHeads.predQuery(Match(12, 0, 1, 0), phrases));
   // std::cerr << "Found head " << a.start << "," << a.pos << "," << a.len << "\n";
   // exit(0);
   std::cerr << "N star " << nStar << "\n";
   docBoundaries.push_back(_sn);
   if(verbose) std::cerr << "Printing docBoundaries" << "\n";
   if(verbose) for(size_t i = 0; i < docBoundaries.size(); i++){ std::cerr << docBoundaries[i] << ", letter: " << _sx[docBoundaries[i]] << "\n";}
   t2 = std::chrono::high_resolution_clock::now();
   lzFactorizeTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to compute matching statistics: " << lzFactorizeTime << " milliseconds\n";

   t1 = std::chrono::high_resolution_clock::now();
   std::cerr << "Start Sorting procedure for MSGSA\n";
   uint32_t *prefSumBucketLengthsStar = new uint32_t[_n + 1];
   prefSumBucketLengthsStar[0] = 0;
   if(verbose) std::cerr << prefSumBucketLengthsStar[0] << "\n";
   for(uint32_t i = 1; i < _n; i++){
      //t_sum += bucketLengths[i-1];
      prefSumBucketLengthsStar[i] = prefSumBucketLengthsStar[i-1] + bucketLengthsStar[i-1];
      if(verbose) std::cerr << prefSumBucketLengthsStar[i] << "\n";
   }
   prefSumBucketLengthsStar[_n] = nStar;

   std::vector<SufSStar> sStar;
   sStar.resize(nStar);
   //SufSStar *sStar = new SufSStar[nStar];

   Match firstHead, secondHead;
   ndoc = 0;
   for(size_t i = 0; i < phrases.size() - 1; i++){
      if(verbose) std::cerr << "i: " << i << "\n";
      firstHead = phrases[i];
      secondHead = phrases[i+1];
      if(firstHead.start == 0){
         ndoc++;
         //iCurrentDoc = 0;
      }
      if(verbose) std::cerr << "doc " << ndoc << " firstHead.start,pos,len: " << firstHead.start << ","
      << firstHead.pos << "," << firstHead.len << "; secondHead.start,pos,len: " << secondHead.start << ","
      << secondHead.pos << "," << secondHead.len << "\n";
      if(secondHead.start == 0){
         if(verbose) std::cerr << "End of doc " << ndoc << "\n";
         //if((typeArray[firstHead.start + docBoundaries[ndoc - 1]] == 0) & (typeArray[firstHead.start + docBoundaries[ndoc - 1] - 1] == 1)){
         sStar[prefSumBucketLengthsStar[_ISA[firstHead.pos]] + (bucketLengthsStar[_ISA[firstHead.pos]]--) - 1] = SufSStar(firstHead.start, ndoc, i, 0);
         //sStar[prefSumBucketLengthsStar[_sx[firstHead.start + docBoundaries[ndoc - 1]]] + (bucketLengthsStar[_sx[firstHead.start + docBoundaries[ndoc - 1]]]--) - 1] = SufSStar(firstHead.start, ndoc, i);
         //}
      }
      else{
         for(uint32_t start = 0; start < secondHead.start - firstHead.start; start++){
            if(firstHead.start + docBoundaries[ndoc - 1] + start != 0){
            if((typeArray[firstHead.start + docBoundaries[ndoc - 1] + start] == 0) & (typeArray[firstHead.start + docBoundaries[ndoc - 1] + start - 1] == 1)){
               sStar[prefSumBucketLengthsStar[_ISA[firstHead.pos + start]] + (bucketLengthsStar[_ISA[firstHead.pos + start]]--) - 1] = SufSStar(firstHead.start + start, ndoc, i, start);
               //sStar[prefSumBucketLengthsStar[_sx[firstHead.start + docBoundaries[ndoc - 1] + start]] + (bucketLengthsStar[_sx[firstHead.start + docBoundaries[ndoc - 1] + start]]--) - 1] = SufSStar(firstHead.start + start, ndoc, i);
            }
            }
         }
      }
   }
   sStar[prefSumBucketLengthsStar[_ISA[secondHead.pos]] + (bucketLengthsStar[_ISA[secondHead.pos]]--) - 1] = SufSStar(secondHead.start, ndoc, phrases.size() - 1, 0);
   //sStar[prefSumBucketLengthsStar[_sx[secondHead.start + docBoundaries[ndoc - 1]]] + (bucketLengthsStar[_sx[secondHead.start + docBoundaries[ndoc - 1]]]--) - 1] = SufSStar(secondHead.start, ndoc, phrases.size() - 1);
   if(verbose) for(size_t x = 0; x < nStar; x++) {
      if(sStar[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      if(verbose) std::cerr << sStar[x].idx << " " << sStar[x].doc << " " << _sx + sStar[x].idx + docBoundaries[sStar[x].doc - 1];
   }
   delete[] typeArray;
   t2 = std::chrono::high_resolution_clock::now();
   uint64_t bucketingTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to bucket suffixes: " << bucketingTime << " milliseconds\n";

   if(verbose) for(uint64_t i = 0; i < _sn; i++){
      std::cerr << _sx[i] << " type: " << typeArray[i] << "\n";
   }

   //put $ instead of X, otherwise the X characters does not lead to a correct comparison (because they are greater)
   for(size_t i = 0; i < _sn; i++) {if(_sx[i] == '%' || _sx[i] == 'X') _sx[i] = '$';}

   t1 = std::chrono::high_resolution_clock::now();
   //Sort suffixes corrisponding to heads
   uint32_t *prefSumBucketLengthsHeads = new uint32_t[_n];
   uint32_t *prefSumBucketLengthsHeadsCopy = new uint32_t[_n+1];
   prefSumBucketLengthsHeads[0] = 0;
   prefSumBucketLengthsHeadsCopy[0] = 0; 
   for(size_t i = 1; i < _n; i++){
      prefSumBucketLengthsHeads[i] = prefSumBucketLengthsHeads[i-1] + bucketLengthsHeads[i-1];
      prefSumBucketLengthsHeadsCopy[i] = prefSumBucketLengthsHeads[i];
   }
   prefSumBucketLengthsHeadsCopy[_n] = phrases.size();
   
   headsSA.resize(phrases.size());
   //headsSA.reserve(phrases.size());
   i = 0, ndoc = 0;
   auto t01 = std::chrono::high_resolution_clock::now();
   for(std::vector<Match>::iterator it = phrases.begin(); it < phrases.end(); it++){
      if(it->start == 0){
         ndoc++;
      }
      //headsSA[prefSumBucketLengthsHeads[_sx[it->start + docBoundaries[ndoc - 1]]]++] = Match(i++, it->pos, ndoc);
      if(verbose) std::cerr << it->start << "," << it->pos << "," << it->len << " doc " << ndoc << " " << _sx + it->start + docBoundaries[ndoc-1] << "\n";
      headsSA[prefSumBucketLengthsHeads[_ISA[it->pos]]++] = MatchSA(i++, it->pos, it->len, !it->smaller, _sx[it->start + docBoundaries[ndoc-1] + it->len]);
      //headsSA.push_back(Match(i++, it->pos, ndoc, it->smaller));
      //prefSumBucketLengthsHeads[_ISA[it->pos]]++;
      //i++;
   }
   auto t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Bucketing heads took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   if(verbose) std::cerr << "Outputting headsSA bucketed (size=" << headsSA.size() << ")\n";
   //if(verbose) for(size_t i = 0; i < headsSA.size(); i++){std::cerr << headsSA[i].start << " " << headsSA[i].pos << " " << headsSA[i].len << " " << (data_type)_sx + phrases[headsSA[i].start].start + docBoundaries[headsSA[i].len - 1] << "\n";}
   std::vector<MatchSA>::iterator begHeads = headsSA.begin();
   //radixSortPos(headsSA, 0, headsSA.size());
   t01 = std::chrono::high_resolution_clock::now();
   //uint32_t *buckets = new uint32_t[0x100]();
   //uint32_t *startIndex = new uint32_t[0x100]();
   for(size_t i = 1; i < _n + 1; i++){
      if(verbose) std::cerr << "headBucket " << prefSumBucketLengthsHeadsCopy[i-1] << " to " << prefSumBucketLengthsHeadsCopy[i] << "\n";
      //std::sort(begHeads + prefSumBucketLengthsHeadsCopy[i-1], begHeads + prefSumBucketLengthsHeadsCopy[i], compareHeadsSA);
      // radixSortChar(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      // uint32_t zeros = radixSortSmaller(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      // radixSortLen(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i-1]+zeros, buckets, startIndex);
      // radixSortLenDecr(begHeads, prefSumBucketLengthsHeadsCopy[i-1]+zeros, prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      std::sort(begHeads + prefSumBucketLengthsHeadsCopy[i-1], begHeads + prefSumBucketLengthsHeadsCopy[i], compareMatchSA);
   }
   if(verbose) for(size_t i = 0; i < headsSA.size(); i++){std::cerr << headsSA[i].pos << " " << headsSA[i].len << " " << headsSA[i].smaller << " " << (data_type)headsSA[i].next << "\n";}
   //delete[] buckets;
   //delete[] startIndex;
   // if(verbose) std::cerr << "Last headBucket\n";
   // std::sort(begHeads + prefSumBucketLengthsHeadsCopy[_n-1], headsSA.end(), compareHeadsSA);
   
   // radixSortChar(headsSA, prefSumBucketLengthsHeadsCopy[_n-1], headsSA.size());
   // uint32_t zeros = radixSortSmaller(headsSA, prefSumBucketLengthsHeadsCopy[_n-1], headsSA.size());
   // radixSortLen(headsSA, prefSumBucketLengthsHeadsCopy[_n-1], prefSumBucketLengthsHeadsCopy[_n-1]+zeros);
   // radixSortLenDecr(headsSA, prefSumBucketLengthsHeadsCopy[_n-1]+zeros, headsSA.size());
   
   // std::sort(headsSA.begin(), headsSA.end(), compareHeadsSA);
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Head sort took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";
   
   t01 = std::chrono::high_resolution_clock::now();
   std::cerr << "Going to re-rank heads\n";
   uint32_t *stringHeads = new uint32_t[headsSA.size()+1]; 
   uint64_t rank = 1;
   int64_t prevLen = -1, prevSmall = -1, prevNext = -1;
   prevPos = -1;
   i = 0;
   for(std::vector<MatchSA>::iterator it = headsSA.begin(); it < headsSA.end(); it++){
      if(i >= headBoundaries.size()-1){
         if(it->pos != prevPos || it->len != prevLen || it->smaller != prevSmall || it->next != prevNext){
            rank++;
            prevPos = it->pos;
            prevLen = it->len;
            prevSmall = it->smaller;
            prevNext = it->next;
         }
      }
      stringHeads[i++] = rank;
   }
   std::cerr << "Re-ranked heads\n";
   if(verbose) for(uint64_t i = 0; i < phrases.size(); i++){
      std::cerr << headsSA[i].pos << "," << headsSA[i].len << " --> " << stringHeads[i] << "\n";
   }
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Reranking took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   t01 = std::chrono::high_resolution_clock::now();
   std::cerr << "Going to invert stringHeads\n";
   uint64_t hLen = headsSA.size();
   for (int i = 0; i < hLen; i++) {
      int next = i;

      // Check if it is already
      // considered in cycle
      while(headsSA[next].start < hLen) {

         // Swap the current element according
         // to the order in headsSA
         std::swap(stringHeads[i], stringHeads[headsSA[next].start]);
         int temp = headsSA[next].start;

         // Subtract size of headsSA from an entry in headsSA
         // to make it negative which indicates
         // the corresponding move
         // has been performed
         headsSA[next].start -= hLen;
         next = temp;
      }
   }
   std::vector<MatchSA>().swap(headsSA);
   if(verbose) for(uint64_t i = 0; i < hLen; i++){
      std::cerr << i << "," << phrases[i].pos << "," << phrases[i].len << " --> " << stringHeads[i] << "\n";
   }
   stringHeads[hLen] = 0;
   std::cerr << "Inverted stringHeads\n";
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Inverting stringHeads took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   uint32_t *indicesSA = new uint32_t[hLen+1]();
   // for(uint64_t i = 0; i < phrases.size(); i++){
   //    headsSufArr[i] = phrases[i].pos << 31 + phrases[i].len;
   // }
   t01 = std::chrono::high_resolution_clock::now();
   std::cerr << "Going to compute suffix array of MS-heads\n";
   //suffixsort(stringHeads, indicesSA, headsSA.size(), rank+1, 1);
   sacak_int(stringHeads, indicesSA, hLen+1, rank+1);
   std::cerr << "Computed suffix array of MS-heads\n";
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Computing MS-heads SA took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   // std::cerr << "Checking SA of MS-heads\n";
   // for(int64_t i = 1; i < headsSA.size() - 1; i++){
   //    // uint64_t keyI = (_ISA[phrases[indicesSA[i]].pos] << 31) + phrases[indicesSA[i]].len;
   //    // uint64_t keyII = (_ISA[phrases[indicesSA[i+1]].pos] << 31) + phrases[indicesSA[i+1]].len;
   //    // if(keyI > keyII){
   //    //    std::cerr << "ERROR " << i << "\n";
   //    //    std::cerr << keyI << ", pos: " << _ISA[phrases[indicesSA[i]].pos] << ", len: " << phrases[indicesSA[i]].len 
   //    //    << "\n" << keyII << ", pos: " << _ISA[phrases[indicesSA[i+1]].pos] << ", len: " << phrases[indicesSA[i+1]].len << "\n\n";
   //    // }
   //    //-std::max(indicesSA[i], indicesSA[i+1])
   //    if(memcmp(stringHeads+indicesSA[i], stringHeads+indicesSA[i+1], headsSA.size()+1) > 0){
   //       std::cerr << "ERROR " << i << "\n";//std::cerr << "PROBLEM with " << i-1 << " (" << MSGSA[i-1].idx << "," << MSGSA[i-1].doc << ") and " << i << " (" << MSGSA[i].idx << "," << MSGSA[i].doc << ")\n"; 
   //    }
   // }
   // std::cerr << "Checked SA of MS-heads\n";
   if(verbose) for(uint64_t i = 0; i < phrases.size()+1; i++){
      std::cerr << stringHeads[i] << ", " << indicesSA[i] << "\n";
   }
   delete[] stringHeads;
   t01 = std::chrono::high_resolution_clock::now();
   std::cerr << "Going to permute headsSA\n";
   headsSA.resize(hLen);
   for(uint64_t i = 1; i < hLen+1; i++) {
      headsSA[i-1] = MatchSA(indicesSA[i], phrases[indicesSA[i]].pos, std::upper_bound(std::begin(headBoundaries), std::end(headBoundaries), indicesSA[i]) - std::begin(headBoundaries), phrases[indicesSA[i]].smaller);
      if(verbose) std::cerr << headsSA[i-1].start << "," << _ISA[headsSA[i-1].pos] << "," << headsSA[i-1].len << "," << headsSA[i-1].smaller << "," << headsSA[i-1].next <<"\n";
   }
   std::cerr << "headBoundaries.size(): " << headBoundaries.size() << "\n";
   std::vector<uint32_t>().swap(headBoundaries);
   std::cerr << "Permuted headsSA\n";
   delete[] indicesSA;
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Permuting MS-heads took: " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   t2 = std::chrono::high_resolution_clock::now();
   uint64_t headSortTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to sort heads: " << headSortTime << " milliseconds\n";

   //if(verbose) std::cerr << "Outputting headsSA after suffix sorting\n";
   //if(verbose) for(size_t i = 0; i < headsSA.size(); i++){std::cerr << headsSA[i].start << " " << headsSA[i].pos << " " << headsSA[i].len << " " << _sx + phrases[headsSA[i].start].start + docBoundaries[headsSA[i].len - 1] << "\n";}
   if(verbose){
      uint64_t errHeads = checkHeadsSA(headsSA, phrases.size());
      std::cerr << "N. errors on headsSA: " << errHeads << "\n";
   }
   //exit(0);
   t1 = std::chrono::high_resolution_clock::now();
   if(verbose) std::cerr << "Computing nextPos in headSA\n";
   std::vector<Match>::iterator begPhrases = phrases.begin();
   for(size_t i = 0; i < headsSA.size(); i++){
      //_ISA[headsSA[headA.pos].pos + (nextStartA - headA.start)]
      uint32_t nextStart = phrases[headsSA[i].start].start + phrases[headsSA[i].start].len;
      Match headNextStart = Match(nextStart, 0, headsSA[i].len);
      Match nextHead = *(pHeads.predQuery(headNextStart, begPhrases));
      headsSA[i].pos = _ISA[nextHead.pos + (nextStart - nextHead.start)];
      __builtin_prefetch(&phrases[headsSA[i+1].start]);
   }
   if(verbose) std::cerr << "Computing nextPos in headSA DONE\n";
   if(verbose) std::cerr << "Computing changeP in phrases\n";
   for(size_t i = 0; i < headsSA.size(); i++){
      phrases[headsSA[i].start].changeP(i);
   }
   if(verbose) std::cerr << "Computing changeP in phrases DONE\n";
   if(verbose) std::cerr << "Computing change heads in sStar\n";
   for(size_t i = 0; i < nStar; i++){
      sStar[i].head = phrases[sStar[i].head].pos;
   }
   if(verbose) std::cerr << "Computing change heads in sStar DONE\n";
   if(verbose) std::cerr << "Computing change len and start in headSA\n";
   for(size_t i = 0; i < headsSA.size(); i++){
      uint32_t nextStart = phrases[headsSA[i].start].start + phrases[headsSA[i].start].len;
      Match headNextStart = Match(nextStart, 0, headsSA[i].len);
      Match nextHead = *(pHeads.predQuery(headNextStart, begPhrases));
      headsSA[i].len = phrases[headsSA[i].start].len;
      headsSA[i].start = nextHead.pos;
      __builtin_prefetch(&phrases[headsSA[i+1].start]);
   }
   std::vector<Match>().swap(phrases);
   // Now: 
   // headsSA[i] = (nextHeadRank, nextHeadISA[pos], length, smaller);

   if(verbose) std::cerr << "Computing change len and start in headSA DONE\n";
   std::vector<SufSStar>::iterator begStar = sStar.begin();
   std::cerr << "Starting to sort S*-suffixes\n";
   
   for(uint32_t i = 1; i < _n + 1; i++){
      if(verbose) std::cerr << i << " " << prefSumBucketLengthsStar[i-1] << " " << prefSumBucketLengthsStar[i] << "\n";
      std::sort(begStar + prefSumBucketLengthsStar[i-1], begStar + prefSumBucketLengthsStar[i], compareSuf);
   }
   std::vector<MatchSA>().swap(headsSA);
   
   if(verbose) for(size_t x = 0; x < nStar; x++) {
      if(sStar[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      if(verbose) std::cerr << sStar[x].idx << " " << sStar[x].doc << " " << sStar[x].head << " " << _sx + sStar[x].idx + docBoundaries[sStar[x].doc - 1];
   }

   if(verbose){
      uint64_t errSStar = checkGSA(sStar, nStar);
      std::cerr << "N. errors on sStar: " << errSStar << "\n";
   }

   
   t2 = std::chrono::high_resolution_clock::now();
   uint64_t sortTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "S*-suffixes sorted in: " << sortTime << " milliseconds\n";
   std::cerr << "number of diffPos " << diffSufPos << "\n";
   std::cerr << "number of diffLen " << diffSufLen << "\n";
   std::cerr << "number of diffHeads " << diffSufHeads << "\n";

   t1 = std::chrono::high_resolution_clock::now();
   uint64_t *prefSumCharBkts = new uint64_t[sizeChars + 1];
   uint64_t *prefSumCharBktsEnds = new uint64_t[sizeChars + 1];
   //uint32_t t_sum = 0;
   prefSumCharBkts[0] = 0;
   prefSumCharBktsEnds[0] = 0;
   if(verbose) std::cerr << prefSumCharBkts[0] << "\n";
   for(size_t i = 1; i < sizeChars; i++){
      //t_sum += bucketLengths[i-1];
      prefSumCharBkts[i] = prefSumCharBkts[i-1] + charBkts[i-1];
      //if(verbose) std::cerr << prefSumBucketLengths[i] << "\n";
   }
   prefSumCharBkts[sizeChars] = _sn;
   for(size_t i = 0; i < sizeChars; i++){
      prefSumCharBktsEnds[i] = prefSumCharBkts[i+1];
   }

   std::cerr << "Going to convert types\n";
   // //change back original positions in heads
   // for(size_t i = 0; i < headsSA.size(); i++){
   //    phrases[i].changeP(headsSA[phrases[i].pos].pos);
   // }
   std::vector<Suf> MSGSA;
   MSGSA.reserve(_sn);
   uint64_t diffLen;
   //smallSStar.reserve(nStar);
   //for(std::vector<SufSStar>::iterator it = sStar.begin(); it < sStar.end(); it++){
   std::reverse(sStar.begin(), sStar.end());
   for(uint32_t x = 1; x < sizeChars; x++){
      //diffLen = (prefSumCharBkts[x] - prefSumCharBkts[x-1]) - (prefSumBucketLengthsStar[x] - prefSumBucketLengthsStar[x-1]);
      diffLen = (prefSumCharBkts[x] - prefSumCharBkts[x-1]) - bucketLengthStarChar[x-1];
      for(uint64_t p = 0; p < diffLen; p++){
         MSGSA.push_back(Suf());
      }
      //for(uint32_t p = 0; p < (prefSumBucketLengthsStar[x] - prefSumBucketLengthsStar[x-1]); p++){
      for(uint32_t p = 0; p < bucketLengthStarChar[x-1]; p++){
         MSGSA.push_back(Suf(sStar.back()));
         sStar.pop_back();
      }
      sStar.shrink_to_fit();
   }

   std::vector<SufSStar>().swap(sStar);
   if(verbose) for(size_t x = 0; x < _sn; x++) {
      if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      if(verbose) std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
   }

   delete[] bucketLengthStarChar;
   delete[] prefSumBucketLengthsHeads;
   delete[] prefSumBucketLengthsHeadsCopy;
   delete[] prefSumBucketLengthsStar;
   delete[] bucketLengthsHeads;
   delete[] bucketLengthsStar;

   uint32_t maskSign = 1 << 31;
   uint32_t maxNumber = (1 << 31) - 1;
   std::cerr << "Start inducing L-types\n";
   data_type c1 = _sx[_sn-1];
   data_type c0;
   //std::cerr << "c1 " << c1 << "\n";
   Suf j;
   std::vector<Suf>::iterator begGSA = MSGSA.begin();
   std::vector<Suf>::iterator b = MSGSA.begin() + prefSumCharBkts[c1];
   *b++ = ((0 < _sn-1) && (_sx[_sn - 2] < c1)) ? Suf(MSGSA[0].idx, ~MSGSA[0].doc) : MSGSA[0];
   for(uint64_t i = 0; i < _sn; ++i){
      if(MSGSA[i].idx > 0){
         j = MSGSA[i]; 
         //MSGSA[i].doc = (maxNumber > MSGSA[i].doc) ? MSGSA[i].doc | maskSign : MSGSA[i].doc & maxNumber;
         MSGSA[i].changeDocSign();
         //if(maxNumber > j.doc){
         if(0 < j.doc){
            if((c0 = _sx[j.idx + docBoundaries[j.doc - 1] - 1]) != c1) { prefSumCharBkts[c1] = b - begGSA; b = begGSA + prefSumCharBkts[c1 = c0]; }
            //MSGSA[prefSumCharBkts[c1]++] = ((0 < j.idx - 1) && (_sx[j.idx + docBoundaries[j.doc - 1] - 2] < c1)) ? Suf(j.idx - 1, ~j.doc) : Suf(j.idx - 1, j.doc);
            *b++ = ((0 < j.idx - 1) && (_sx[j.idx + docBoundaries[j.doc - 1] - 2] < c1)) ? Suf(j.idx - 1, ~j.doc) : Suf(j.idx - 1, j.doc);
         }
      }
      __builtin_prefetch(&_sx[MSGSA[i+1].idx + docBoundaries[MSGSA[i+1].doc - 1] - 1]);
   }
   std::cerr << "\nAfter inducing L-types\n";
   if(verbose) for(size_t x = 0; x < _sn; x++) {
      if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      if(MSGSA[x].doc < 0){
         std::cerr << MSGSA[x].idx << " " << (~MSGSA[x].doc) << " " << _sx + MSGSA[x].idx + docBoundaries[(~MSGSA[x].doc) - 1];
      }
      else{
         std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
      } 
   }
   
   std::cerr << "Start inducing S-types\n";
   b = MSGSA.begin() + prefSumCharBktsEnds[c1 = 0];
   for(uint64_t i = _sn - 1; i < _sn; i--){
      //if(verbose) std::cerr << "i: " << i << " " << j.idx << "," << j.doc << "\n";
      if(MSGSA[i].idx > 0){
         //if(maxNumber > MSGSA[i].doc){
         if(0 < MSGSA[i].doc){
            j = MSGSA[i];
            if((c0 = _sx[j.idx + docBoundaries[j.doc - 1] - 1]) != c1) { prefSumCharBktsEnds[c1] = b - begGSA; b = begGSA + prefSumCharBktsEnds[c1 = c0]; }
            *--b = ((0 == j.idx - 1) || (_sx[j.idx + docBoundaries[j.doc - 1] - 2] > c1)) ? Suf(j.idx - 1, ~j.doc) : Suf(j.idx - 1, j.doc);
         }
         else{
            //MSGSA[i].doc = MSGSA[i].doc & maxNumber;
            MSGSA[i].changeDocSign();
         }
      }
      //else if(maxNumber < MSGSA[i].doc) MSGSA[i].doc = MSGSA[i].doc & maxNumber;
      else if(0 > MSGSA[i].doc) MSGSA[i].changeDocSign();
      __builtin_prefetch(&_sx[MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1] - 1]);
   }
   std::cerr << "\nAfter inducing S-types\n";
   if(verbose) for(size_t x = 0; x < _sn; x++) {
      if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
   }

   t2 = std::chrono::high_resolution_clock::now();
   uint64_t induceTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Induced in: " << induceTime << " milliseconds\n";

   int checkGSA = 0;
   if(checkGSA){
      std::cerr << "Checking GSA\n"; 
      uint32_t err = 0;
      for(size_t i = 0; i < _sn; i++){
      if(verbose) std::cerr << "i=" << i << ": " << MSGSA[i].idx << " " << MSGSA[i].doc << " " << "\n";//MSGSA[i].head <<"\n";
      
      data_type *_slice_sx = _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1];
      data_type *_slice_prev;
      uint32_t maxIdx;
      if(i > 0){
         if(MSGSA[i].doc == 0 || MSGSA[i-1].doc == 0){
            std::cerr << "There was an empty entry\n";
            err++;
            continue;
         }
         _slice_prev = _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1];
         maxIdx = std::min(docBoundaries[MSGSA[i].doc] - (MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1]), docBoundaries[MSGSA[i-1].doc] - (MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1]));
      } 
      else{
         _slice_prev = (data_type *)"$";
         maxIdx = 1;
      }
      if(verbose) std::cerr << "suf_i-1 " << _slice_prev;
      if(verbose) std::cerr << "suf_i " << _slice_sx << "\n";
      
      if(memcmp(_slice_sx, _slice_prev, maxIdx) < 0){
         if(verbose) std::cerr << "PROBLEM with " << i-1 << " (" << MSGSA[i-1].idx << "," << MSGSA[i-1].doc << ") and " << i << " (" << MSGSA[i].idx << "," << MSGSA[i].doc << ")\n"; 
         err++;
         //if(err) break;
      }
      }
      std::cerr << "n. errors " << err << "\n"; 
   } 
   std::cerr << "maxCounter " << maxCounter << "\n";
   std::cerr << "meanCounter " << sumCounter/(denCounter+0.00000001) << "\n";
   std::cerr << "times it had to compare only one char " << diffLenCounter << "\n";
   std::cerr << "times it had to compare more than one char " << denCounter << "\n";
   std::cerr << "times it compared two suff in const time " << finalSuffCounter << "\n";
   //std::cerr << "n. of ties " << tiesCounter << "\n";
//  delete[] sx;
//  delete[] bucketLengths;
//  delete[] prefSumBucketLengths;
//  delete[] prefSumBucketLengthsCopy;
   delete[] _LCP;
   delete[] _ISA;
   delete[] _SA;
   std::vector<Suf>().swap(MSGSA);
    //delete[] GSA;
    
    //Serialize reference, phrases, and other info
    //File format:
    //size_t _r: length of reference
    //size_t [] _reference: _r uint8_ts, the referene
    //size_t _r: length of reference <--- yes, again
    //size_t [] sa: _r uint32_ts, the suffix array of the reference (discarded after load)
    //size_t _z: number of phrases
    //size_t [] starts: starting positions of phrases in collection (discarded after load)
    //size_t _z: number of phrases <--- yes, again
    //uint32_t [] _phrases: sources of phrases (positions in reference)
    //size_t _n: total length of the collection including separator symbols

    //std::cerr << "Writing out to file: " << outputfilename << std::endl;
    //std::ofstream fout(outputfilename, std::ios::out | std::ios::binary);

    //std::cout << "Reference: " << _n << " items, file size =  " <<  _n * sizeof(unsigned int) << "\n";
    ////size_t size = positionsCovered; // for the reference without unused symbols
    //size_t size = _n;
    //std::cout << "Writing out reference: ";
    //for (int j = 0; j < 10; j++) std::cout << _x[j] << ' ';
    //std::cout << " ... (" << size << " items)\n";
    //fout.write((char *) &size, sizeof(size_t));
    //fout.write((char *) &_x[0], size * sizeof(data_type));

    //std::cout << "Writing out _SA: ";
    //for (int j = 0; j < 10; j++) std::cout << _SA[j] << ' ';
    //std::cout << " ... (" << size << " items)\n";
    //fout.write((char *) &size, sizeof(size_t));
    //fout.write((char *) _SA, size * sizeof(uint32_t));

    //size = starts.size();
    //std::cout << "Writing out starts: ";
    //for (int j = 0; j < 10; j++) std::cout << starts[j] << ' ';
    //std::cout << " ... (" << size << " items)\n";
    //fout.write((char *) &size, sizeof(size_t));
    //fout.write((char *) &starts[0], starts.size() * sizeof(filelength_type));

    //size = sources.size();
    //std::cout << "Writing out sources: ";
    //for (int j = 0; j < 10; j++) std::cout << sources[j] << ' ';
    //std::cout << " ... (" << size << " items)\n";
    //fout.write((char *) &size, sizeof(size_t));
    //fout.write((char *) &sources[0], sources.size() * sizeof(uint32_t));


    //fout.write((char *) &_sn, sizeof(size_t));

    //fout.close();
    /*
    uint64_t maxSuffixesBefore = 0;
    uint32_t zerosInSuffixesBefore = 0;
    uint64_t sum = 0;
    for(uint32_t j=0; j<_n; j++){
       if(suffixesBefore[j] > maxSuffixesBefore) maxSuffixesBefore = suffixesBefore[j];
       if(!suffixesBefore[j]) zerosInSuffixesBefore++;
       bucketStarts[j] = sum;
       sum += suffixesBefore[j];
    }

    std::cerr << "After prefix sum.\n";

    //std::vector<std::pair<uint32_t,uint32_t> > sortedPhrases;
    //sortedPhrases.reserve(phrases.size());
    std::pair<uint32_t,uint32_t> *sortedPhrases = new std::pair<uint32_t,uint32_t>[phrases.size()];
    
    std::cerr << "Allocated sortedPhrases.\n";

    uint32_t nphrases = 0;
    for(uint32_t j=0; j<phrases.size(); j++){
       uint32_t possa = phrases[j].first;
       uint32_t len = phrases[j].second;
       if(len){
          uint64_t bs = bucketStarts[possa];
          //TODO: set sortedPhrases[bs].first to be phrase id (i.e. j) 
          sortedPhrases[bs] = phrases[j];
          bucketStarts[possa]++;
          nphrases++;
       }
    }
    std::cerr << "After bucketing. nphrases: " << nphrases << '\n';

    //reset bucket starts
    sum = 0;
    for(uint32_t j=0; j<_n; j++){
       bucketStarts[j] = sum;
       sum += suffixesBefore[j];
    }
    std::cerr << "Bucket starts reset." << '\n';

    for(uint32_t j=0; j<_n; j++){
       if(suffixesBefore[j]){
          //std::cerr << "Sorting bucket of length: " << suffixesBefore[j] << '\n';
          sort(sortedPhrases+bucketStarts[j],sortedPhrases+bucketStarts[j]+suffixesBefore[j],compareMatchesWithSamePosition);
       }
    }
    std::cerr << "After length sorting of buckets: " << nphrases << '\n';
    
    std::ofstream fout(outputfilename, std::ios::out);
    fout << "Outputting sorted phrases" << "\n";
    for(uint32_t x=0; x<phrases.size(); x++){ 
       //if(suffixesBefore[x]){
         fout << sortedPhrases[x].first << " " << sortedPhrases[x].second << "\n";
       //}
       //else{
       //   fout << "It was empty for " << x << "\n";
       //}
    }
    fout.close();

    uint32_t previousLen = 0;
    uint64_t numberOfLengthBuckets = 0;
    uint64_t lengthBucketSize = 0, maxLengthBucketSize = 0;
    for(uint32_t j=0; j<nphrases; j++){
       if(sortedPhrases[j].second != previousLen){
          numberOfLengthBuckets++;
          if(lengthBucketSize > maxLengthBucketSize){
             maxLengthBucketSize = lengthBucketSize;
          }
       }else{
          lengthBucketSize++;
       }
       previousLen = sortedPhrases[j].second;
    }

    std::cerr << "number of length buckets: " << numberOfLengthBuckets << '\n';
    std::cerr << "max. length bucket size: " << maxLengthBucketSize << '\n';

    std::cerr << "number of factors: " << numfactors << '\n';
    std::cerr << "average factor length: " << (_sn/numfactors) << '\n';
    std::cerr << "max. factor length: " << maxFactorLength << '\n';
    std::cerr << "lenZeroFactors: " << lenZeroFactors << '\n';
    std::cerr << "number of phrases with unambiguous match: " << _numberOfSingleMatches << '\n';
    std::cerr << "number of phrases shorter than max. LCP of reference: " << _numberOfShortFactors << '\n';
    std::cerr << "max. in suffixesBefore: " << maxSuffixesBefore << '\n';
    std::cerr << "zeroes in suffixesBefore: " << zerosInSuffixesBefore << '\n';
    std::cerr << "---Time to lz factorize: " << lzFactorizeTime << " milliseconds\n";
    std::cerr << "phrases.size() " << phrases.size() << '\n';
    */
    return numfactors;
}

void computeLZFactorAt(filelength_type i, filelength_type *pos, filelength_type *len, int64_t & leftB, int64_t & rightB, int64_t & maxMatch, bool & isSmallerThanMaxMatch, unsigned char &mismatchingSymbol) {
    filelength_type offset = *len;
    filelength_type j = i + offset;
    //*pos = i;
    //*len = 0;

    //std::cerr << "Here at least?" << i << "\n";
    //treat runs of N's in a special way
   //  if(_sx[i] == 'N'){
   //     //std::cerr << "Hit a run of Ns... \n";
   //     //std::cerr.flush();
   //     uint64_t start = i;
   //     while(_sx[i] == 'N' && _sx[i]  != '%'){ //file should be terminated with an X, so no need to check length ---> && i < _sn){
   //        i++;
   //     }
   //     mismatchingSymbol = _sx[i];
   //     *len = i - start;
   //     *pos = _n;
   //     //std::cerr << "Hit a run of Ns, " << *len << " symbols long.\n";
   //     return;
   //  }
    //std::cerr << "After.\n";


    //int64_t nlb = 0, nrb = _n - 1;
    int64_t nlb = leftB, nrb = rightB;
    unsigned int match = _SA[nlb];
    //std::cout << "match " << match << "\n";
    //std::cout << "_sx[" <<j << "]= " << _sx[j] << "\n";
    while (j < _sn) { //scans the string from j onwards until a maximal prefix is found between _x and _sx
        //std::cout << "j: " << j << "\n";
        //std::cerr << "j = " << j << " nlb: " << nlb << " nrb: " << nrb << "\n";
        if (nlb == nrb) { 
            //std::cout << "Search finished with nlb == nrb " << nlb << " " << nrb << "\n";
            if (_x[_SA[nlb] + offset] != _sx[j]) {
                //std::cout << "mismatch " << _x[_SA[nlb] + offset] << " and " << _sx[j] << "\n";
                //fprintf(stderr,"Breaking from 1\n");
                isSmallerThanMaxMatch = (_x[_SA[nlb] + offset] > _sx[j]);
                mismatchingSymbol = _sx[j];
                break;
            }
            leftB = nlb;
            rightB = nrb;
            maxMatch = nlb;
        } else { //refining the bucket in which the match is found, from left and then from right
            renormalizations++;
            nlb = binarySearchLB(nlb, nrb, offset, _sx[j]);
            //std::cerr << "nlb: " << nlb << "\n";
            if (nlb < 0) {
                //no match, the game is up
                //fprintf(stderr,"Breaking from 2; offset = %lu; _sx[%lu] = %u\n",offset,j,_sx[j]);
                maxMatch = -(nlb)-1;
                isSmallerThanMaxMatch = true;
                mismatchingSymbol = _sx[j];
                if(maxMatch == nrb+1){
                   maxMatch--;
                   isSmallerThanMaxMatch = false;
                }
                match = _SA[maxMatch];
                break;
            }
            nrb = binarySearchRB(nlb, nrb, offset, _sx[j]);
            //std::cout << "nrb after binary search " << nrb << "\n";
            //std::cerr << "nrb: " << nrb << "\n";
            leftB = nlb;
            rightB = nrb;
        }
        //std::cerr << "After if nlb: " << nlb << "\n";
        match = _SA[nlb];
        //std::cout << "Match after binary search " << match << "\n";
        //std::cerr << "match: " << match << "\n";
        j++;
        offset++;
    }
    *pos = match;
    *len = offset;
    //std::cout << "Match " << match << "\n";
    //std::cout << "Len " << offset << "\n";
}

//Returns the leftmost occurrence of the element if it is present or (if not present)
//then returns -(x+1) where x is the index at which the key would be inserted into the 
//array: i.e., the index of the first element greater than the key, or hi+1 if all elements 
//in the array are less than the specified key.
inline int64_t binarySearchLB(int64_t lo, int64_t hi, filelength_type offset, data_type c) {
   int64_t low = lo, high = hi;
   while (low <= high) {
      int64_t mid = (low + high) >> 1;
      data_type midVal = _x[_SA[mid] + offset];
      if (midVal < c)
         low = mid + 1;
      else if (midVal > c)
         high = mid - 1;
      else { //midVal == c
         if (mid == lo)
               return mid; // leftmost occ of key found
         data_type midValLeft = _x[_SA[mid - 1] + offset];
         if (midValLeft == midVal) {
               high = mid - 1; //discard mid and the ones to the right of mid
         } else { //midValLeft must be less than midVal == c
               return mid; //leftmost occ of key found
         }
      }
   }
   return -(low + 1);  // key not found.
}

inline int64_t binarySearchRB(int64_t lo, int64_t hi, filelength_type offset, data_type c) {
   int64_t low = lo, high = hi;
   while (low <= high) {
      int64_t mid = (low + high) >> 1;
      data_type midVal = _x[_SA[mid] + offset];
      if (midVal < c)
         low = mid + 1;
      else if (midVal > c)
         high = mid - 1;
      else { //midVal == c
         if (mid == hi)
               return mid; // rightmost occ of key found
         data_type midValRight = _x[_SA[mid + 1] + offset];
         if (midValRight == midVal) {
               low = mid + 1; //discard mid and the ones to the left of mid
         } else { //midValRight must be greater than midVal == c
               return mid; //rightmost occ of key found
         }
      }
   }
   return -(low + 1);  // key not found.
}

