#include <parallel/algorithm>
#include <chrono>
#include <ctime>
#include <iostream>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string.h>
#include <cstdlib>
#include <fstream>
#include <sstream>

#include "mmsearch.h"
#include "rmq_tree.h"
#include "utils.h"
#include "match.h"
#include "predecessor.h"
#include "qsufsort.c"
#include "gsa-is/gsacak.c"
//#include "libdivsufsort/build/include/divsufsort.h"
#include "sais-lite-2.4.1/sais.c"
#include "inplace-radixxx/inplace_radixxx.h"

#define likely(x)       __builtin_expect((x),1)

void computeLZFactorAt(filelength_type i, filelength_type *pos, filelength_type *len, int64_t &leftB, int64_t &rightB, int64_t &match, bool &isSmaller, unsigned char &mismatchingSymbol);
inline int64_t binarySearchLB(int64_t lo, int64_t hi, filelength_type offset, data_type c);
inline int64_t binarySearchRB(int64_t lo, int64_t hi, filelength_type offset, data_type c);

static std::string outputFile;

//static data_type *_x;
static std::string _x;
static int *_SA;
static uint32_t *_ISA;
static uint32_t *_LCP;
static uint32_t *_PLCP;
static rmq_tree *_rmq;
static uint32_t _n;
static data_type *_sx;
static filelength_type _sn;
static bool _isMismatchingSymbolNeeded;
static std::vector<uint32_t> docBoundaries;
static std::vector<uint32_t> headBoundaries;
static predecessor2 pHeads;

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

uint16_t sizeChars = 256;
uint64_t D = 0;

//std::vector<std::pair<uint32_t,uint32_t> > phrases;
std::vector<Match> phrases;
std::vector<MatchSA> headsSA;

//LCP array construction method of J. Kärkkäinen, G. Manzini, and S. J. Puglisi, CPM 2009
void constructLCP(std::string t, int32_t n, int32_t *sa, uint32_t *lcp, uint32_t *temp) {
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

void constructISA(int32_t *sa, uint32_t *isa, uint32_t n){
   fprintf(stderr,"\tComputing ISA...\n");
   for(uint32_t i=0; i<n; i++){
      isa[sa[i]] = i;
   }
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

void radixSortPosInplace(const std::vector<SufSStar>::iterator a, const uint32_t start, const uint32_t end){
   int RADIX = 0x100;
   std::vector<SufSStar> result;
   result.resize(end-start);  
   uint32_t *buckets = new uint32_t[RADIX](); 
   uint32_t *startIndex = new uint32_t[RADIX]();
   data_type key = 0;
   for(uint32_t flag = 0; flag < 4; flag++){
      for(std::vector<SufSStar>::iterator it = a+start; it < a+end; ++it){
         key = it->diffLen.bytearray[flag];
         //std::cerr << "key: " << (uint32_t)key << "\n";
         ++buckets[key];
      }
   }
}

void radixSortPos(const std::vector<SufSStar>::iterator a, const uint32_t start, const uint32_t end, const uint8_t radixIter){
   const int RADIX = 0x100;
   std::vector<SufSStar> result;
   result.resize(end-start);  
   uint32_t *buckets = new uint32_t[RADIX](); 
   uint32_t *startIndex = new uint32_t[RADIX]();
   data_type key = 0;
   for(uint32_t flag = 0; flag < radixIter; flag++){
      //std::cerr << "flag: " << flag << "\n";
      for(std::vector<SufSStar>::iterator it = a+start; it < a+end; ++it) {
         //key = (it->pos & (MASK << flag)) >> flag;
         key = it->diffLen.bytearray[flag];
         //std::cerr << "key: " << (uint32_t)key << "\n";
         ++buckets[key];
      }
      startIndex[0] = 0;
      for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j - 1];
      for(std::vector<SufSStar>::iterator it = a+end-1; it >= a+start; --it){
         //key = (it->pos & (MASK << flag)) >> flag;
         key = it->diffLen.bytearray[flag];
         //if(key!=0) std::cerr << "key: " << (uint32_t)key << "\n";
         result[startIndex[key] + --buckets[key]].assign(it->idx, it->doc, it->head, it->diffLen.val);
      }
      std::copy(result.begin(), result.end(), a+start);
      //flag += MASK_BIT_LENGTH;
   }
   //std::reverse(a.begin()+start, a.begin()+end);
   delete[] buckets;
   delete[] startIndex;
}

// void radixSortPos(const std::vector<SufSStar>::iterator a, const uint32_t start, const uint32_t end){
//    const uint32_t INT_BIT_SIZE = sizeof(uint32_t)<<3; int RADIX = 256 * 256, MASK = RADIX-1, MASK_BIT_LENGTH = 8;
//    std::vector<SufSStar> result;
//    result.resize(end-start);  
//    uint32_t *buckets = new uint32_t[RADIX](); 
//    uint32_t *startIndex = new uint32_t[RADIX]();
//    uint16_t key = 0;
//    for(uint32_t flag = 0; flag < 2; flag++){
//       std::cerr << "flag: " << flag << "\n";
//       for(std::vector<SufSStar>::iterator it = a+start; it < a+end; ++it) {
//          //key = (it->pos & (MASK << flag)) >> flag;
//          key = it->diffLen.doublebytearray[flag];
//          //std::cerr << "key: " << key << "\n";
//          ++buckets[key];
//       }
//       startIndex[0] = 0;
//       for(uint32_t j = 1; j < RADIX; ++j) startIndex[j] = startIndex[j - 1] + buckets[j - 1];
//       for(std::vector<SufSStar>::iterator it = a+end-1; it >= a+start; --it){
//          //key = (it->pos & (MASK << flag)) >> flag;
//          key = it->diffLen.doublebytearray[flag];
//          //if(key!=0) std::cerr << "key: " << (uint32_t)key << "\n";
//          result[startIndex[key] + --buckets[key]].assign(it->idx, it->doc, it->head, it->diffLen.val);
//       }
//       std::copy(result.begin(), result.end(), a+start);
//       //flag += MASK_BIT_LENGTH;
//    }
//    //std::reverse(a.begin()+start, a.begin()+end);
//    delete[] buckets;
//    delete[] startIndex;
// }

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
   if(headA.len - a.diffLen.val != headB.len - b.diffLen.val){
      //diffSufLen++;
      return headA.smaller*((headA.len - a.diffLen.val) < (headB.len - b.diffLen.val)) + 
            !headB.smaller*((headA.len - a.diffLen.val) > (headB.len - b.diffLen.val));
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
   uint64_t err = -1;
   #pragma omp parallel for
   for(size_t i = 0; i < n; i++){
       if(verbose) std::cerr << "i=" << i << ": " << GSA[i].idx << " " << GSA[i].doc << " " << "\n";//MSGSA[i].head <<"\n";
       if(GSA[i].doc == 0 || GSA[i-1].doc == 0){
          std::cerr << "There was an empty entry\n";
          #pragma omp atomic
          err++;
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
         std::cerr << "PROBLEM with " << i-1 << " (" << GSA[i-1].idx << "," << GSA[i-1].doc << ") and " << i << " (" << GSA[i].idx << "," << GSA[i].doc << ")\n"; 
         #pragma omp atomic
         err++;
      }
    }
    return err;
}

void lzInitialize(data_type *ax, unsigned int an, bool isMismatchingSymbolNeeded, char *refFileName, char *collFileName) {
   auto t1 = std::chrono::high_resolution_clock::now();

   auto t01 = std::chrono::high_resolution_clock::now();
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
   docBoundaries.push_back(0);
   uint64_t *maxRunsCollection = new uint64_t[sizeChars]();
   for(uint64_t i = 0; i < sn; i++){
      if(sx[i] == '%'){
         D++;
         docBoundaries.push_back(i+1);
      }
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
   docBoundaries.push_back(_sn);

   //std::string refAug(_x);
   for(uint16_t i = 0; i < sizeChars; i++){
      if(verbose) std::cerr << (char)i << " ref: " << maxRunsReference[i] << ", coll: " << maxRunsCollection[i] << "\n";
      if((maxRunsReference[i] == 0) & (maxRunsCollection[i] != 0) & (i != '%')){
         for(uint64_t x = 0; x < maxRunsCollection[i]; x++){
            _x += (char)i;
         }
      }
   }
   _x += '$';
   _x += '\n';
   //docBoundaries.reserve(maxRunsCollection['%']);
   headBoundaries.reserve(maxRunsCollection['%']);
   //std::cerr << refAug << "\n";
   auto t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Augmenting reference done in " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   // char refAugFileName[256];
   // sprintf(refAugFileName, "%s.aug", refFileName);
   // std::ofstream fout(refAugFileName, std::ios::out | std::ios::binary);
   // fout.write(_x.c_str(), _x.size());
   // fout.close();
   t01 = std::chrono::high_resolution_clock::now();
   int *sa = new int[_x.size()];
   sais(reinterpret_cast<unsigned char*>(const_cast<char*>(_x.c_str())), sa, _x.size());
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Computing SA done in " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   // /* Allocate 5blocksize bytes of memory. */
   // char saFileName[1024]; 
   // sprintf(saFileName, "%s.sa", refAugFileName);
   // char command[2048];
   // sprintf(command, "libdivsufsort/build/examples/./mksary %s %s", refAugFileName, saFileName);
   // system(command);

   // fprintf(stderr, "About to read SA of ref\n");
   // std::cerr << saFileName << '\n';
   // infile = fopen(saFileName, "r");
   // if (!infile) {
   //    fprintf(stderr, "Error opening suffix array of input file %s\n", saFileName);
   //    exit(1);
   // }
   // unsigned int san = 0;
   // fseek(infile, 0, SEEK_END);
   // san = ftell(infile) / sizeof(unsigned int);
   // std::cerr << "san = " << san << '\n';
   // fseek(infile, 0, SEEK_SET);
   // unsigned int *sa = new unsigned int[san];
   // if (san != fread(sa, sizeof(unsigned int), san, infile)) {
   //    fprintf(stderr, "Error reading sa from file\n");
   //    exit(1);
   // }
   // fclose(infile);
   
   //_x = refAug.c_str();
   //std::string().swap(refAug);
   _sx = sx;
   _sn = sn - 1;
   std::cerr << "Last pos " << _sx + _sn - 1 << "\n";
   _n = _x.size();

   t01 = std::chrono::high_resolution_clock::now();
   _SA = sa;
   _ISA = new uint32_t[_n];
   _PLCP = new uint32_t[_n];
   _LCP = new uint32_t[_n];
   t01 = std::chrono::high_resolution_clock::now();
   constructISA(_SA,_ISA,_n);
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Computing ISA done in " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   constructLCP(_x,_n,_SA,_LCP,_PLCP);
   for(int32_t i = 0; i < _n; i++){
      _PLCP[i] = std::max(_LCP[_ISA[i]],_LCP[_ISA[i]+1]);
   }
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Computing LCP and PLCP done in " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";
   // for(uint32_t i=0;i<_n;i++){
   //    if(_LCP[i] > _maxLCP & _x[_SA[i]] != 'N') _maxLCP = _LCP[i];
   // }
   // std::cerr << "_maxLCP = " << _maxLCP << '\n';

   t01 = std::chrono::high_resolution_clock::now();
   fprintf(stderr,"\tComputing RMQ...\n");
   _rmq = new rmq_tree((int *)_LCP, _n, 7);
   t02 = std::chrono::high_resolution_clock::now();
   std::cerr << "Computing RMQ done in " << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01).count() << " ms\n";

   _isMismatchingSymbolNeeded = isMismatchingSymbolNeeded;
   std::cerr << "Finished pre-processing\n";
   //TODO: preprocess SA and store intervals containing all suffixes with a given short prefix
   auto t2 = std::chrono::high_resolution_clock::now();
   uint64_t preprocTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Preprocessing done in " << preprocTime << " ms\n";
   sprintf(collFileName, "%s.gsa", collFileName);
   outputFile = std::string(collFileName);

}

int lzFactorize(char *fileToParse, int seqno, char* outputfilename, const bool v) {
   verbose = v;
   omp_set_num_threads(4);
   std::cerr << "File is in memory\n";
   auto t1 = std::chrono::high_resolution_clock::now();

   unsigned int numfactors = 0;

   unsigned int inc = 100000000;
   uint64_t mark = inc;

   std::cerr << "About to start main parsing loop...\n";

   int64_t leftB = 0;
   int64_t rightB = _n-1;
   int64_t match;
   bool isSmallerThanMatch;
   unsigned char mismatchingSymbol;
   int64_t prevPos = -2;
   uint64_t pos = 0, len = 0;
   uint32_t ndoc = 1;
   uint32_t iCurrentDoc = 0;
   //uint32_t *bucketLengths = new uint32_t[_n]();
   uint32_t *bucketLengthsStar = new uint32_t[_n]();
   //uint32_t *bucketLengthsStar = new uint32_t[sizeChars]();
   uint32_t *bucketLengthStarChar = new uint32_t[sizeChars]();
   uint32_t *bucketLengthsHeads = new uint32_t[_n]();
   //uint32_t *bucketLengthsHeads = new uint32_t[sizeChars]();
   if(verbose) for(size_t s = 0; s < _n; s++){
      std::cerr << s << "\t" << _SA[s] << "\t" << _x[_SA[s]];
   }

   int64_t nStar = 0;
   // bool *typeArray = new bool[_sn];
   // typeArray[_sn - 1] = 0;
   // for(uint64_t i = _sn - 2; i < _sn; i--){
   //    if(_sx[i] < _sx[i+1]){
   //       typeArray[i] = 0;
   //    }
   //    else if(_sx[i] == _sx[i+1]){
   //       typeArray[i] = typeArray[i+1];
   //    }
   //    else{
   //       typeArray[i] = 1;
   //       if(typeArray[i+1] == 0) nStar++;
   //    }
   // }
   // docBoundaries.push_back(0);
   headBoundaries.push_back(0);
   uint64_t i = 0;
   uint64_t *charBkts = new uint64_t[sizeChars]();
   uint64_t maxValue = 0;
   phrases.reserve(_sn / 10);
   uint64_t sumLen = 0, maxLen = 0;
   uint64_t heurYes = 0, heurNo = 0;
   while(i < _sn){
      if(verbose) std::cerr << "i: " << i << "\n";
      if(i > mark){
         fprintf(stderr,"i = %lu; lpfRuns = %ld\n",i,phrases.size());
         mark = mark + inc;
      }
      sumLen += len;
      if(len > maxLen) maxLen = len;
      charBkts[_sx[i]]++;
      if(_sx[i] == '%'){ //new doc found
         leftB = 0;
         rightB = _n-1;
         len = 0;
         pos = _n - 1;
         phrases.push_back(Match(iCurrentDoc, pos, len, 0));
         //docBoundaries.push_back(iCurrentDoc + 1 + docBoundaries[ndoc-1]); 
         headBoundaries.push_back(phrases.size());
         if(maxValue < iCurrentDoc) maxValue = iCurrentDoc;
         iCurrentDoc = 0;
         ndoc++;
      }
      else{
         computeLZFactorAt(i, &pos, &len, leftB, rightB, match, isSmallerThanMatch, mismatchingSymbol);
         if((int64_t)pos != prevPos+1){
            phrases.push_back(Match(iCurrentDoc, pos, len, isSmallerThanMatch));
         }
         iCurrentDoc++;
         len--;
         
         if(leftB == rightB){
            while(len > _PLCP[pos+1]){
            //while(len > _maxLCP){
               //sumLen += len;
               //if(len > maxLen) maxLen = len;
               i++;
               charBkts[_sx[i]]++;
               iCurrentDoc++;
               len--;
               pos++;
               heurYes++;
            }
            leftB = rightB = _ISA[pos];
         }
         std::pair<int,int> interval = contractLeft(leftB,rightB,len);
         leftB = interval.first;
         rightB = interval.second;
         heurNo++;
      }
      i++;
      prevPos = pos;
   }
   delete[] _SA;
   delete[] _LCP;
   delete[] _PLCP;
   
   //delete[] _rmq;
   std::cerr << "heurYes " << heurYes << ", heurNo " << heurNo << "\n";
   //std::cerr << "maxLen " << maxLen << " meanLen " << (float)sumLen/_sn << "\n";
   phrases.shrink_to_fit();
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
   for(uint64_t i = 0; i < phrases.size(); i++){
      bucketLengthsHeads[_ISA[phrases[i].pos]]++;
   }
   std::cerr << "N star " << nStar << "\n";
   // docBoundaries.push_back(_sn);
   if(verbose) std::cerr << "Printing docBoundaries" << "\n";
   if(verbose) for(size_t i = 0; i < docBoundaries.size(); i++){ std::cerr << docBoundaries[i] << ", letter: " << _sx[docBoundaries[i]] << "\n";}
   auto t2 = std::chrono::high_resolution_clock::now();
   uint64_t lzFactorizeTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to compute matching statistics: " << lzFactorizeTime << " milliseconds\n";

   t1 = std::chrono::high_resolution_clock::now();
   std::cerr << "Start Sorting procedure for MSGSA\n";

   std::vector<SufSStar> sStar;
   std::vector<SufSStar>::iterator begStar;
   uint32_t *prefSumBucketLengthsStar = new uint32_t[_n + 1]();
   prefSumBucketLengthsStar[0] = 0;
   Match firstHead, secondHead;
   ndoc = 0;
   uint64_t sufNumber = 0;
   if(_n < 256*256){
      bucketLengthsStar[_ISA[phrases[phrases.size()-1].pos]]++;
      bucketLengthStarChar['%']++;
      nStar++;
      bool currentType = 0;
      ndoc = D;
      for(uint64_t i = phrases.size()-2; i > 0; i--){
         secondHead = phrases[i];
         firstHead = phrases[i-1];
         if(secondHead.start == 0){
            bucketLengthsStar[_ISA[firstHead.pos]]++;
            bucketLengthStarChar['%']++;
            currentType = 0;
            nStar++;
            ndoc--; 
            //std::cerr << "doc: " << ndoc << "\n";
         }
         else{
            for(int32_t start = secondHead.start - firstHead.start - 1; start >= 0; start--){
               if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType =  1;
               }
               else if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] < _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType = 0;
               }
               if(firstHead.start + start != 0){
                  if((currentType == 0) & (_sx[firstHead.start + docBoundaries[ndoc - 1] + start - 1] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start])){
                     bucketLengthsStar[_ISA[firstHead.pos + start]]++;
                     bucketLengthStarChar[_sx[firstHead.start + docBoundaries[ndoc - 1] + start]]++;
                     nStar++;
                  }
               }
            }
         }
      }
      sStar.resize(nStar);
      begStar = sStar.begin();

      if(verbose) std::cerr << prefSumBucketLengthsStar[0] << "\n";
      for(uint32_t i = 1; i < _n; i++){
         prefSumBucketLengthsStar[i] = prefSumBucketLengthsStar[i-1] + bucketLengthsStar[i-1];
      }
      prefSumBucketLengthsStar[_n] = nStar;

      sStar[prefSumBucketLengthsStar[_ISA[phrases[phrases.size()-1].pos]]++].assign(phrases[phrases.size()-1].start, D, phrases.size() - 1, 0);
      //nStar--;
      currentType = 0;
      ndoc = D;
      for(uint64_t i = phrases.size()-2; i > 0; i--){
         secondHead = phrases[i];
         firstHead = phrases[i-1];
         if(secondHead.start == 0){
            ndoc--; 
            sStar[prefSumBucketLengthsStar[_ISA[firstHead.pos]]++].assign(firstHead.start, ndoc, i-1, 0);
            currentType = 0;
            //nStar--;
            //std::cerr << "doc: " << ndoc << "\n";
         }
         else{
            for(int32_t start = secondHead.start - firstHead.start - 1; start >= 0; start--){
               if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType =  1;
               }
               else if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] < _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType = 0;
               }
               if(firstHead.start + start != 0){
                  if((currentType == 0) & (_sx[firstHead.start + docBoundaries[ndoc - 1] + start - 1] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start])){
                     sStar[prefSumBucketLengthsStar[_ISA[firstHead.pos + start]]++].assign(firstHead.start + start, ndoc, i-1, start);
                     //nStar--;
                  }
               }
            }
         }
      }

      prefSumBucketLengthsStar[0] = 0;
      for(uint32_t i = 1; i < _n; i++){
         prefSumBucketLengthsStar[i] = prefSumBucketLengthsStar[i-1] + bucketLengthsStar[i-1];
         //if(verbose) std::cerr << prefSumBucketLengthsStar[bkt] << "\n";
      }
      prefSumBucketLengthsStar[_n] = nStar;
   }
   else{
      uint32_t max = _n;
      uint32_t shift;
		for(uint8_t i = 0; i < 48; i++){
			if(max < nOfDigitsBig[i]){
				shift = i;
				break;
			}
		} 
      uint8_t radixIter = 2;
      if(shift < 8){
         radixIter--;
      }
      uint64_t *preBuckets = new uint64_t[65536]();

      preBuckets[_ISA[phrases[phrases.size()-1].pos] >> shift]++;
      bucketLengthStarChar['%']++;
      nStar++;
      bool currentType = 0;
      ndoc = D;
      for(uint64_t i = phrases.size()-2; i > 0; i--){
         secondHead = phrases[i];
         firstHead = phrases[i-1];
         if(secondHead.start == 0){
            preBuckets[_ISA[firstHead.pos] >> shift]++;
            bucketLengthStarChar['%']++;
            currentType = 0;
            nStar++;
            ndoc--; 
            //std::cerr << "doc: " << ndoc << "\n";
         }
         else{
            for(int32_t start = secondHead.start - firstHead.start - 1; start >= 0; start--){
               if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType =  1;
               }
               else if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] < _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType = 0;
               }
               if(firstHead.start + start != 0){
                  if((currentType == 0) & (_sx[firstHead.start + docBoundaries[ndoc - 1] + start - 1] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start])){
                     preBuckets[_ISA[firstHead.pos + start] >> shift]++;
                     bucketLengthStarChar[_sx[firstHead.start + docBoundaries[ndoc - 1] + start]]++;
                     nStar++;
                  }
               }
            }
         }
      }
      sStar.resize(nStar);
      begStar = sStar.begin();
      std::cerr << "NSTAR is now: " << nStar << "\n";
      std::cerr << "Counted preBuckets\n";
      uint64_t *prefSumPreBuckets = new uint64_t[65536];
      prefSumPreBuckets[0] = 0;
      for(uint32_t i = 1; i < 65536; i++){
         prefSumPreBuckets[i] = prefSumPreBuckets[i-1] + preBuckets[i-1];
      }
      std::cerr << "PrefSumPreBuckets\n";

      sStar[prefSumPreBuckets[_ISA[phrases[phrases.size()-1].pos] >> shift]++].assign(phrases[phrases.size()-1].start, D, phrases.size() - 1, _ISA[phrases[phrases.size()-1].pos]);
      //nStar--;
      currentType = 0;
      ndoc = D;
      for(uint64_t i = phrases.size()-2; i > 0; i--){
         secondHead = phrases[i];
         firstHead = phrases[i-1];
         if(secondHead.start == 0){
            ndoc--; 
            sStar[prefSumPreBuckets[_ISA[firstHead.pos] >> shift]++].assign(firstHead.start, ndoc, i-1, _ISA[firstHead.pos]);
            currentType = 0;
            //nStar--;
            //std::cerr << "doc: " << ndoc << "\n";
         }
         else{
            for(int32_t start = secondHead.start - firstHead.start - 1; start >= 0; start--){
               if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType =  1;
               }
               else if(_sx[firstHead.start + docBoundaries[ndoc - 1] + start] < _sx[firstHead.start + docBoundaries[ndoc - 1] + start + 1]){
                  currentType = 0;
               }
               if(firstHead.start + start != 0){
                  if((currentType == 0) & (_sx[firstHead.start + docBoundaries[ndoc - 1] + start - 1] > _sx[firstHead.start + docBoundaries[ndoc - 1] + start])){
                     sStar[prefSumPreBuckets[_ISA[firstHead.pos + start] >> shift]++].assign(firstHead.start + start, ndoc, i-1, _ISA[firstHead.pos + start]);
                     //nStar--;
                  }
               }
            }
         }
      }
      std::cerr << "Bucketed S*-suffixes\n";
      prefSumPreBuckets[0] = 0;
      for(uint32_t i = 1; i < 65536; i++){
         prefSumPreBuckets[i] = prefSumPreBuckets[i-1] + preBuckets[i-1];
      }
      std::cerr << "Radix iter: " << (uint32_t)radixIter << "\n";
      //#pragma omp parallel for schedule(dynamic)
      for(uint32_t i = 1; i < 65536; i++){
         //std::cerr << "radix sorting i: " << i << "\n";
         //inplace_radixxx::rsort(begStar + prefSumPreBuckets[i-1], begStar + prefSumPreBuckets[i], [](const SufSStar &a){return a.diffLen.val;});
         if(prefSumPreBuckets[i]-prefSumPreBuckets[i-1])
            radixSortPos(begStar, prefSumPreBuckets[i-1], prefSumPreBuckets[i], radixIter);
         //std::sort(begStar + prefSumPreBuckets[i-1], begStar + prefSumPreBuckets[i], [](const SufSStar a, const SufSStar b){return a.diffLen.val < b.diffLen.val;});
      }
      //std::sort(sStar.begin(), sStar.end(), [](const SufSStar a, const SufSStar b){return a.diffLen.val < b.diffLen.val;});
      //radixSortPos(sStar.begin(), 0 , nStar);
      //inplace_radixxx::rsort(sStar.begin(), sStar.end(), [](const SufSStar &a){return a.diffLen.val;});
      
      for(std::vector<SufSStar>::iterator it = sStar.begin(); it < sStar.end(); it++){
         bucketLengthsStar[it->diffLen.val]++;
         //if(verbose) std::cerr << prefSumBucketLengthsStar[bkt] << "\n";
      }
      if(verbose) std::cerr << prefSumBucketLengthsStar[0] << "\n";
      for(uint32_t i = 1; i < _n; i++){
         prefSumBucketLengthsStar[i] = prefSumBucketLengthsStar[i-1] + bucketLengthsStar[i-1];
         //if(verbose) std::cerr << prefSumBucketLengthsStar[bkt] << "\n";
      }
      prefSumBucketLengthsStar[_n] = nStar;
      delete[] preBuckets;
      delete[] prefSumPreBuckets;
   }
   delete[] bucketLengthsStar;
   std::cerr << "Prefix sum done\n";
   std::cerr << "NStar: " << nStar << "\n";

   t2 = std::chrono::high_resolution_clock::now();
   uint64_t bucketingTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Time to bucket suffixes: " << bucketingTime << " milliseconds\n";

   // if(verbose) for(uint64_t i = 0; i < _sn; i++){
   //    std::cerr << _sx[i] << " type: " << typeArray[i] << "\n";
   // }
   // delete[] typeArray;
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
      //if(verbose) std::cerr << it->start << "," << it->pos << "," << it->len << " doc " << ndoc << " " << _sx + it->start + docBoundaries[ndoc-1] << "\n";
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
      //if(verbose) std::cerr << "headBucket " << prefSumBucketLengthsHeadsCopy[i-1] << " to " << prefSumBucketLengthsHeadsCopy[i] << "\n";
      //std::sort(begHeads + prefSumBucketLengthsHeadsCopy[i-1], begHeads + prefSumBucketLengthsHeadsCopy[i], compareHeadsSA);
      // radixSortChar(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      // uint32_t zeros = radixSortSmaller(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      // radixSortLen(begHeads, prefSumBucketLengthsHeadsCopy[i-1], prefSumBucketLengthsHeadsCopy[i-1]+zeros, buckets, startIndex);
      // radixSortLenDecr(begHeads, prefSumBucketLengthsHeadsCopy[i-1]+zeros, prefSumBucketLengthsHeadsCopy[i], buckets, startIndex);
      std::sort(begHeads + prefSumBucketLengthsHeadsCopy[i-1], begHeads + prefSumBucketLengthsHeadsCopy[i], compareMatchSA);
   }
   if(verbose) for(size_t i = 0; i < headsSA.size(); i++){std::cerr << headsSA[i].pos << " " << headsSA[i].len << " " << headsSA[i].smaller << " " << (data_type)headsSA[i].next << "\n";}
   delete[] prefSumBucketLengthsHeads;
   delete[] prefSumBucketLengthsHeadsCopy;
   delete[] bucketLengthsHeads;
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
   int temp, next;
   for (int i = 0; i < hLen; i++) {
      next = i;

      // Check if it is already
      // considered in cycle
      while(headsSA[next].start < hLen) {

         // Swap the current element according
         // to the order in headsSA
         std::swap(stringHeads[i], stringHeads[headsSA[next].start]);
         temp = headsSA[next].start;

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
   std::cerr << "Computing nextPos in headSA\n";
   std::vector<Match>::iterator begPhrases = phrases.begin();
   for(size_t i = 0; i < headsSA.size(); i++){
      //_ISA[headsSA[headA.pos].pos + (nextStartA - headA.start)]
      uint32_t nextStart = phrases[headsSA[i].start].start + phrases[headsSA[i].start].len;
      Match headNextStart = Match(nextStart, 0, headsSA[i].len);
      Match nextHead = *(pHeads.predQuery(headNextStart, begPhrases));
      headsSA[i].pos = _ISA[nextHead.pos + (nextStart - nextHead.start)];
      __builtin_prefetch(&phrases[headsSA[i+1].start]);
   }
   std::cerr << "Computing nextPos in headSA DONE\n";
   std::cerr << "Computing changeP in phrases\n";
   for(size_t i = 0; i < headsSA.size(); i++){
      phrases[headsSA[i].start].changeP(i);
   }
   std::cerr << "Computing changeP in phrases DONE\n";
   std::cerr << "Computing change heads in sStar\n";
   for(size_t i = 0; i < nStar; i++){
      sStar[i].diffLen.val = sStar[i].idx - phrases[sStar[i].head].start;
      //if( sStar[i].diffLen.val) std::cerr << "diffLen: " << sStar[i].diffLen.val << " idx: " << sStar[i].idx << " start: " << phrases[sStar[i].head].start <<"\n";
      sStar[i].head = phrases[sStar[i].head].pos;
   }
   std::cerr << "Computing change heads in sStar DONE\n";
   std::cerr << "Computing change len and start in headSA\n";
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

   std::cerr << "Computing change len and start in headSA DONE\n";
   std::cerr << "Starting to sort S*-suffixes\n";
   
   for(uint32_t i = 1; i < _n + 1; i++){
      //if(verbose) std::cerr << i << " " << prefSumBucketLengthsStar[i-1] << " " << prefSumBucketLengthsStar[i] << "\n";
      std::sort(begStar + prefSumBucketLengthsStar[i-1], begStar + prefSumBucketLengthsStar[i], compareSuf);
   }
   std::vector<MatchSA>().swap(headsSA);
   delete[] prefSumBucketLengthsStar;

   if(verbose) for(size_t x = 0; x < nStar; x++) {
      if(sStar[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
      if(verbose) std::cerr << sStar[x].idx << " " << sStar[x].doc << " " << sStar[x].head << " " << _sx + sStar[x].idx + docBoundaries[sStar[x].doc - 1];
   }
   
   t2 = std::chrono::high_resolution_clock::now();
   uint64_t sortTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "S*-suffixes sorted in: " << sortTime << " milliseconds\n";
   std::cerr << "number of diffPos " << diffSufPos << "\n";
   std::cerr << "number of diffLen " << diffSufLen << "\n";
   std::cerr << "number of diffHeads " << diffSufHeads << "\n";

   if(verbose){
      uint64_t errSStar = checkGSA(sStar, nStar);
      std::cerr << "N. errors on sStar: " << errSStar << "\n";
   }
   //exit(0);

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
   std::vector<std::pair<uint32_t, int32_t>> MSGSA;
   MSGSA.reserve(_sn);
   uint64_t diffLen;
   //smallSStar.reserve(nStar);
   //for(std::vector<SufSStar>::iterator it = sStar.begin(); it < sStar.end(); it++){
   std::reverse(sStar.begin(), sStar.end());
   
   for(uint32_t x = 1; x < sizeChars; x++){
      //diffLen = (prefSumCharBkts[x] - prefSumCharBkts[x-1]) - (prefSumBucketLengthsStar[x] - prefSumBucketLengthsStar[x-1]);
      diffLen = (prefSumCharBkts[x] - prefSumCharBkts[x-1]) - bucketLengthStarChar[x-1];
      for(uint64_t p = 0; p < diffLen; p++){
         //MSGSA.push_back(Suf());
         MSGSA.push_back(std::make_pair(0,0));
      }
      //for(uint32_t p = 0; p < (prefSumBucketLengthsStar[x] - prefSumBucketLengthsStar[x-1]); p++){
      for(uint32_t p = 0; p < bucketLengthStarChar[x-1]; p++){
         //MSGSA.push_back(Suf(sStar.back()));
         MSGSA.push_back(std::make_pair(sStar.back().idx, sStar.back().doc));
         sStar.pop_back();
      }
      if(bucketLengthStarChar[x-1]) sStar.shrink_to_fit();
   }

   std::vector<SufSStar>().swap(sStar);
   // if(verbose) for(size_t x = 0; x < _sn; x++) {
   //    if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
   //    if(verbose) std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
   // }

   delete[] bucketLengthStarChar;
   
   //uint32_t maskSign = 1 << 31;
   //uint32_t maxNumber = (1 << 31) - 1;
   std::cerr << "Start inducing L-types\n";
   data_type c1 = _sx[_sn-1];
   data_type c0;
   //std::cerr << "c1 " << c1 << "\n";
   std::pair<uint32_t, int32_t> j;
   std::vector<std::pair<uint32_t, int32_t>>::iterator begGSA = MSGSA.begin();
   std::vector<std::pair<uint32_t, int32_t>>::iterator b = MSGSA.begin() + prefSumCharBkts[c1];
   *b++ = ((0 < _sn-1) && (_sx[_sn - 2] < c1)) ? std::pair<uint32_t, int32_t>(MSGSA[0].first, ~MSGSA[0].second) : MSGSA[0];
   for(uint64_t i = 0; i < _sn; ++i){
      if(MSGSA[i].first > 0){
         j = MSGSA[i]; 
         //MSGSA[i].doc = (maxNumber > MSGSA[i].doc) ? MSGSA[i].doc | maskSign : MSGSA[i].doc & maxNumber;
         
         //MSGSA[i].changeDocSign();
         MSGSA[i].second = ~MSGSA[i].second;
         //if(maxNumber > j.doc){
         if(0 < j.second){
            if((c0 = _sx[j.first + docBoundaries[j.second - 1] - 1]) != c1) { prefSumCharBkts[c1] = b - begGSA; b = begGSA + prefSumCharBkts[c1 = c0]; }
            //MSGSA[prefSumCharBkts[c1]++] = ((0 < j.idx - 1) && (_sx[j.idx + docBoundaries[j.doc - 1] - 2] < c1)) ? Suf(j.idx - 1, ~j.doc) : Suf(j.idx - 1, j.doc);
            *b++ = ((0 < j.first - 1) && (_sx[j.first + docBoundaries[j.second - 1] - 2] < c1)) ? std::pair<uint32_t, int32_t>(j.first - 1, ~j.second) : std::pair<uint32_t, int32_t>(j.first - 1, j.second);
         }
      }
      //__builtin_prefetch(&_sx[MSGSA[i+1].idx + docBoundaries[MSGSA[i+1].doc - 1] - 1]);
   }
   std::cerr << "\nAfter inducing L-types\n";
   // if(verbose) for(size_t x = 0; x < _sn; x++) {
   //    if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
   //    if(MSGSA[x].doc < 0){
   //       std::cerr << MSGSA[x].idx << " " << (~MSGSA[x].doc) << " " << _sx + MSGSA[x].idx + docBoundaries[(~MSGSA[x].doc) - 1];
   //    }
   //    else{
   //       std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
   //    } 
   // }
   
   std::cerr << "Start inducing S-types\n";
   b = MSGSA.begin() + prefSumCharBktsEnds[c1 = 0];
   for(uint64_t i = _sn - 1; i < _sn; i--){
      //if(verbose) std::cerr << "i: " << i << " " << j.idx << "," << j.doc << "\n";
      if(MSGSA[i].first > 0){
         //if(maxNumber > MSGSA[i].doc){
         if(0 < MSGSA[i].second){
            j = MSGSA[i];
            if((c0 = _sx[j.first + docBoundaries[j.second - 1] - 1]) != c1) { prefSumCharBktsEnds[c1] = b - begGSA; b = begGSA + prefSumCharBktsEnds[c1 = c0]; }
            *--b = ((0 == j.first - 1) || (_sx[j.first + docBoundaries[j.second - 1] - 2] > c1)) ? std::pair<uint32_t, int32_t>(j.first - 1, ~j.second) : std::pair<uint32_t, int32_t>(j.first - 1, j.second);
         }
         else{
            //MSGSA[i].doc = MSGSA[i].doc & maxNumber;
            //MSGSA[i].changeDocSign();
            MSGSA[i].second = ~MSGSA[i].second;
         }
      }
      //else if(maxNumber < MSGSA[i].doc) MSGSA[i].doc = MSGSA[i].doc & maxNumber;
      else if(0 > MSGSA[i].second) MSGSA[i].second = ~MSGSA[i].second;; //MSGSA[i].changeDocSign();
      //__builtin_prefetch(&_sx[MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1] - 1]);
   }
   std::cerr << "\nAfter inducing S-types\n";
   t2 = std::chrono::high_resolution_clock::now();
   uint64_t induceTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   std::cerr << "Induced in: " << induceTime << " milliseconds\n";

   // if(verbose) for(size_t x = 0; x < _sn; x++) {
   //    if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
   //    std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
   // }
   // std::fstream file;
   // file.open(outputFile.c_str(), std::ios_base::out);
   // std::ostream_iterator<Suf> outItr(file);
   // std::copy(MSGSA.begin(), MSGSA.end(), outItr);
   // file.close();
   
   // FILE *ofp;
   // ofp = fopen(outputFile.c_str(), "wb");
   // fwrite(MSGSA.data(), sizeof(std::pair<uint32_t, int32_t>), MSGSA.size(), ofp);
   // fclose(ofp);

   // THIS ONE
   // t1 = std::chrono::high_resolution_clock::now();
   // std::ofstream ofp (outputFile, std::ios_base::binary);
   // ofp.write(reinterpret_cast<const char*>(&MSGSA[0]), sizeof(std::pair<uint32_t, int32_t>)*MSGSA.size());

   // ofp.close();
   // // //fclose(ofp);
   // t2 = std::chrono::high_resolution_clock::now();
   // uint64_t writeTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
   // std::cerr << "Results written in: " << writeTime << " milliseconds\n";
   int checkGSA = 0;
   if(checkGSA){
      std::cerr << "Checking GSA\n"; 
      uint32_t err = 0;
      #pragma omp parallel for
      for(size_t i = 0; i < _sn; i++){
         if(verbose) std::cerr << "i=" << i << ": " << MSGSA[i].first << " " << MSGSA[i].second << " " << "\n";//MSGSA[i].head <<"\n";
         
         data_type *_slice_sx = _sx + MSGSA[i].first + docBoundaries[MSGSA[i].second - 1];
         data_type *_slice_prev;
         uint32_t maxIdx;
         if(i > 0){
            if(MSGSA[i].second == 0 || MSGSA[i-1].second == 0){
               std::cerr << "There was an empty entry\n";
               err++;
               continue;
            }
            _slice_prev = _sx + MSGSA[i-1].first + docBoundaries[MSGSA[i-1].second - 1];
            maxIdx = std::min(docBoundaries[MSGSA[i].second] - (MSGSA[i].first + docBoundaries[MSGSA[i].second - 1]), docBoundaries[MSGSA[i-1].second] - (MSGSA[i-1].first + docBoundaries[MSGSA[i-1].second - 1]));
         } 
         else{
            _slice_prev = (data_type *)"$";
            maxIdx = 1;
         }
         if(verbose) std::cerr << "suf_i-1 " << _slice_prev;
         if(verbose) std::cerr << "suf_i " << _slice_sx << "\n";
         
         if(memcmp(_slice_sx, _slice_prev, maxIdx) < 0){
            if(verbose) std::cerr << "PROBLEM with " << i-1 << " (" << MSGSA[i-1].first << "," << MSGSA[i-1].second << ") and " << i << " (" << MSGSA[i].first << "," << MSGSA[i].second << ")\n"; 
            err++;
            //if(err) break;
         }
      }
      std::cerr << "n. errors " << err << "\n"; 
   } 
   // std::cerr << "maxCounter " << maxCounter << "\n";
   // std::cerr << "meanCounter " << sumCounter/(denCounter+0.00000001) << "\n";
   // std::cerr << "times it had to compare only one char " << diffLenCounter << "\n";
   // std::cerr << "times it had to compare more than one char " << denCounter << "\n";
   // std::cerr << "times it compared two suff in const time " << finalSuffCounter << "\n";
   // delete[] _LCP;
   // delete[] _ISA;
   // delete[] _SA;
   // std::vector<Suf>().swap(MSGSA);

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

