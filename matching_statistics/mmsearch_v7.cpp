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

#include "mmsearch.h"
#include "rmq_tree.h"
#include "utils.h"

void computeLZFactorAt(filelength_type i, filelength_type *pos, filelength_type *len, int64_t &leftB, int64_t &rightB, int64_t &match, bool &isSmaller, unsigned char &mismatchingSymbol);
inline int64_t binarySearchLB(int64_t lo, int64_t hi, filelength_type offset, data_type c);
inline int64_t binarySearchRB(int64_t lo, int64_t hi, filelength_type offset, data_type c);

static data_type *_x;
static unsigned int *_SA;
static uint32_t *_ISA;
static uint32_t *_LCP;
static rmq_tree *_rmq;
static uint32_t _n;
static data_type *_sx;
static filelength_type _sn;
static bool _isMismatchingSymbolNeeded;
static std::vector<uint32_t> docBoundaries;
static std::vector<uint32_t> headBoundaries;

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
uint64_t diffLen = 0;
uint64_t finalSuffCounter = 0;

struct Match{
   //uint64_t suf; //position of suffix in collection
   uint32_t start; //position in the collection 
   uint32_t pos; //position of match in _reference
   uint32_t len; //length of match
   //unsigned char next; //symbol in the collection after the match
   Match(){}
   //Match(uint32_t p, uint32_t l, unsigned char nxt){
   //   pos = p; len = l, next = nxt;
   //}
   Match(uint32_t s, uint32_t p, uint32_t l){
      start = s; pos = p; len = l;
   }
   void changeS(uint32_t s){
      start = s;
   }
   void changeP(uint32_t p){
      pos = p;
   }
};

//std::vector<std::pair<uint32_t,uint32_t> > phrases;
std::vector<Match> phrases;
std::vector<Match> headsSA;

struct Suf{
   uint32_t idx;
   uint32_t doc;
   Suf(){idx = 0; doc = 0;}
   Suf(uint32_t i, uint32_t d){
      idx = i; doc = d;
   }
};


struct SuffixComparator{
   const uint32_t *_maximalMatchRanks;
   SuffixComparator(uint32_t *maximalMatchRanks){
      _maximalMatchRanks = maximalMatchRanks;
   }
   bool operator()(const Match &i1, const Match &i2){ 
      //comparison code using _maximalMatchRanks
      return true;
   }
};

//LCP array construction method of J. Kärkkäinen, G. Manzini, and S. J. Puglisi, CPM 2009
void constructLCP(unsigned char *t, int32_t n, uint32_t *sa, uint32_t *lcp, uint32_t *temp) {
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

inline std::vector<Match>::iterator getHead(Suf a){
   std::vector<Match>::iterator head = std::upper_bound(phrases.begin() + headBoundaries[a.doc-1], phrases.begin() + headBoundaries[a.doc], Match(a.idx, 0, 0), 
   [](const Match a, const Match b){
      return a.start < b.start;
   });
   return head-1;
}

bool compareSuf(const Suf &a, const Suf &b){
   std::vector<Match>::iterator headA = getHead(a);
   std::vector<Match>::iterator headB = getHead(b);
   uint32_t nextMM = std::min(headA->len - (a.idx - headA->start), headB->len - (b.idx - headB->start));
   if (_sx[a.idx + docBoundaries[a.doc - 1] + nextMM] != _sx[b.idx + docBoundaries[b.doc - 1] + nextMM]){
      diffLen++;
      return _sx[a.idx + docBoundaries[a.doc - 1] + nextMM] < _sx[b.idx + docBoundaries[b.doc - 1] + nextMM];
   }
   if(headA->len == 0){
      return a.doc < b.doc;
   }
   headA++;
   headB++;
   uint32_t counter = 0;
   while(headA->len == headB->len){
      sumCounter++;
      counter++;
      if(maxCounter < counter) maxCounter = counter;
      if(headA->len == 0){
         denCounter++;
         return a.doc < b.doc;
      }
      if(headA->pos != headB->pos){
         denCounter++;
         return _ISA[headA->pos] < _ISA[headB->pos];
      }
      // if(_sx[headA->start + docBoundaries[a.doc - 1] + headA->len] != _sx[headB->start + docBoundaries[b.doc - 1] + headB->len]){
      //    return _sx[headA->start + docBoundaries[a.doc - 1] + headA->len] < _sx[headB->start + docBoundaries[b.doc - 1] + headB->len];
      // }
      uint32_t nextStartA = headA->start + headA->len;
      uint32_t nextStartB = headB->start + headB->len;
      headA = std::upper_bound(headA, phrases.begin() + headBoundaries[a.doc], Match(nextStartA, 0, 0), 
         [](const Match a, const Match b){return a.start < b.start;}) - 1;
      headB = std::upper_bound(headB, phrases.begin() + headBoundaries[b.doc], Match(nextStartB, 0, 0), 
         [](const Match a, const Match b){return a.start < b.start;}) - 1;    
      if((headA->start - nextStartA) != (headB->start - nextStartB)){
         denCounter++;
         return _ISA[headA->pos - (headA->start - nextStartA)] < _ISA[headB->pos - (headB->start - nextStartB)];
      }
   }
   denCounter++;
   if(headA->pos != headB->pos){return _ISA[headA->pos] < _ISA[headB->pos];}
   nextMM = std::min(headA->len, headB->len);
   return _sx[headA->start + docBoundaries[a.doc - 1] + nextMM] < _sx[headB->start + docBoundaries[b.doc - 1] + nextMM];

}


void lzInitialize(data_type *ax, unsigned int *sa, unsigned int an, bool isMismatchingSymbolNeeded) {
    _x = ax;
    _n = an;
    _SA = sa;
    _ISA = new uint32_t[_n];
    _LCP = new uint32_t[_n];
    constructLCP(_x,_n,_SA,_LCP,_ISA);
    for(uint32_t i=0;i<_n;i++){
       if(_LCP[i] > _maxLCP) _maxLCP = _LCP[i];
    }
    std::cerr << "_maxLCP = " << _maxLCP << '\n';
    constructISA(_SA,_ISA,_n);
    fprintf(stderr,"\tComputing RMQ...\n");
    _rmq = new rmq_tree((int *)_LCP, _n, 7);
    _isMismatchingSymbolNeeded = isMismatchingSymbolNeeded;
    //TODO: preprocess SA and store intervals containing all suffixes with a given short prefix
}

int lzFactorize(char *fileToParse, int seqno, char* outputfilename, bool v) {
    verbose = v;
    FILE *infile = fopen(fileToParse, "r");
    if(!infile){
        fprintf(stderr, "Error opening file of sequence %d (%s)\n", seqno, fileToParse);
        exit(1);
    }
    filelength_type sn = 0;
    fseek(infile, 0L, SEEK_END);
    sn = ftello(infile) / sizeof(data_type);
    std::cerr << "sn: " << sn << '\n';
    fseek(infile, 0L, SEEK_SET);
    data_type *sx = new data_type[sn + 1];
    if(sn != fread(sx, sizeof(data_type), sn, infile)){
        fprintf(stderr, "Error reading %lu bytes from file %s\n", sn, fileToParse);
        exit(1);
    }
    sx[sn] = 1; //I don't think there is any reason to do this
    fclose(infile);

    std::cerr << "File is in memory\n";
    auto t1 = std::chrono::high_resolution_clock::now();

    _sx = sx;
    _sn = sn - 1;
    std::cerr << "Last pos " << _sx + _sn - 1 << "\n";

    std::vector<filelength_type> starts;
    std::vector<uint32_t> sources;
    std::vector<uint32_t> lengths;
    std::vector<uint8_t> nextSymbols;

    std::vector<Match> matches;

    unsigned int numfactors = 0;

    unsigned int inc = 100000000;
    uint64_t mark = inc;

    std::vector<Suf> MSGSA;
    MSGSA.resize(_sn);
    //std::pair<uint32_t, uint32_t> *GSA = new std::pair<uint32_t, uint32_t>[_sn];

    std::cerr << "About to start main parsing loop...\n";

    int64_t leftB = 0;
    int64_t rightB = _n-1;
    int64_t match;
    bool isSmallerThanMatch;
    unsigned char mismatchingSymbol;
    int64_t prevPos = -2;
    int64_t lpfRuns = 0;
    uint64_t pos = 0, len = 0;
    docBoundaries.push_back(0);
    uint32_t ndoc = 1;
    uint32_t iCurrentDoc = 0;
    uint32_t *bucketLengths = new uint32_t[_n]();
    uint32_t *bucketLengthsHeads = new uint32_t[_n]();
    if(verbose) for(size_t s = 0; s < _n; s++){
       std::cerr << s << "\t" << _SA[s] << "\t" << _x + _SA[s];
    }
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
    uint64_t i = 0;
    while(i < _sn) {
        //std::cout << "i: " << i << "\n";
        if(i > mark){
           fprintf(stderr,"i = %lu; lpfRuns = %ld\n",i,lpfRuns);
           mark = mark + inc;
        }
        computeLZFactorAt(i, &pos, &len, leftB, rightB, match, isSmallerThanMatch, mismatchingSymbol);
        if(verbose){
          data_type *_slice_sx = _sx + i;
          std::cerr << "S: " << _slice_sx;
          data_type *_slice_x = _x + pos;
          data_type *_slice_sax = _x + _ISA[match];
          std::cerr << "R: " << _x << "--> pos: " << pos << " " << _slice_x << "--> match:" << _slice_sax << "\n";
        } 
        if(_sx[i] == '%'){
           pos = _n;
        }
        if((int64_t)pos != prevPos+1 || len == 0){
        //if(i > 1){
        //if(typeArray[i] == 0 & typeArray[i-1] == 1){
            //phrases.push_back(std::make_pair(match,len));
            phrases.push_back(Match(iCurrentDoc, pos, len));
            bucketLengthsHeads[_ISA[pos]]++;
            //std::cout << "New Phrase\nleftB: " << leftB << " pos: " << pos << " len: " << len << '\n';
            lpfRuns++;
            if(maxFactorLength < len){ maxFactorLength = len; }
            if(len <= _maxLCP){ _numberOfShortFactors++; }
            numfactors++;
            //if(leftB == rightB){
               //suffixesBefore[match]++;
            //}
         }
        //}
        //if(verbose) std::cerr << "Adding one to position pos --> _ISA[pos] --> len: " << pos << "," << _ISA[pos] << "," << len << "\n";
        bucketLengths[_ISA[pos]]++;
        prevPos = pos;
        //std::cerr << "i:" << i << "; pos,ISA[pos],match,len: (" << pos << "," << _ISA[pos] << "," << match << "," << len << ") " << "\n";
        //for(int a = pos; a < pos + len; a++){ std::cerr << _x[a];}
        //std::cerr << "\n";
        //for(int a = i; a < i + len; a++){ std::cerr << _sx[a];}
        //std::cerr << "\n";

        //MSGSA.push_back(Suf(iCurrentDoc, ndoc, _ISA[pos], len));

        iCurrentDoc++;
        if(len == 0 || _sx[i] == '$'){ //new doc found
           pos = (((uint32_t)_sx[i]) | (1<<31)); 
           docBoundaries.push_back(iCurrentDoc + docBoundaries[ndoc-1]); 
           headBoundaries.push_back(phrases.size());
           iCurrentDoc = 0; 
           ndoc++;
        }
        if (len == 0){
           lenZeroFactors++;
           len++;
        }
        i++;
        if(len == 1 || pos == _n){
           //root
           leftB = 0;
           rightB = _n-1;
           len = 0;
        }else{
           //Contract left
           //Prepare for next position
           //std::cout << "Contracting left" << "\n";
           len--;
           if(leftB == rightB && len > _maxLCP){
              leftB = rightB = _ISA[_SA[leftB]+1];
              _numberOfSingleMatches++;
              if(verbose) std::cerr << "No contractLeft\n";
           }else{
              std::pair<int,int> interval = contractLeft(leftB,rightB,len);
              leftB = interval.first;
              rightB = interval.second;
              if(verbose) std::cerr << "Yes contractLeft" << leftB << "," << rightB << "\n";
           }
        }
    }
    //MSGSA.pop_back();
    if(verbose) std::cerr << "Printing docBoundaries" << "\n";
    if(verbose) for(size_t i = 0; i < docBoundaries.size(); i++){ std::cerr << docBoundaries[i] << ", letter: " << _sx[docBoundaries[i]] << "\n";}
    auto t2 = std::chrono::high_resolution_clock::now();
    uint64_t lzFactorizeTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();

    t1 = std::chrono::high_resolution_clock::now();
    std::cerr << "Start Sorting procedure for MSGSA\n";
    uint32_t *prefSumBucketLengths = new uint32_t[_n + 1];
    uint32_t *prefSumBucketLengthsCopy = new uint32_t[_n + 1];
    //uint32_t t_sum = 0;
    prefSumBucketLengths[0] = 0;
    prefSumBucketLengthsCopy[0] = 0;
    if(verbose) std::cerr << prefSumBucketLengths[0] << "\n";
    for(size_t i = 1; i < _n; i++){
       //t_sum += bucketLengths[i-1];
       prefSumBucketLengths[i] = prefSumBucketLengths[i-1] + bucketLengths[i-1];
       if(verbose) std::cerr << prefSumBucketLengths[i] << "\n";
    }
    prefSumBucketLengths[_n] = _sn;
    for(size_t i = 0; i < _n; i++){
       prefSumBucketLengthsCopy[i] = prefSumBucketLengths[i+1]-1;
    }

    //iCurrentDoc = 0;
    ndoc = 0;
    Match firstHead, secondHead;
    std::cerr << "phrases.size(): " << phrases.size() << "\n";
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
          //if(typeArray[firstHead.start + docBoundaries[ndoc - 1]] == 0 & typeArray[firstHead.start + docBoundaries[ndoc - 1] - 1] == 1)
          MSGSA[prefSumBucketLengths[_ISA[firstHead.pos]] + (bucketLengths[_ISA[firstHead.pos]]--) - 1] = Suf(firstHead.start, ndoc);
       }
       else{
          for(uint32_t start = 0; start < secondHead.start - firstHead.start; start++){
             if(firstHead.start + docBoundaries[ndoc - 1] + start != 0){
                if(typeArray[firstHead.start + docBoundaries[ndoc - 1] + start] == 0 & typeArray[firstHead.start + docBoundaries[ndoc - 1] + start - 1] == 1){
                   MSGSA[prefSumBucketLengths[_ISA[firstHead.pos + start]] + (bucketLengths[_ISA[firstHead.pos + start]]--) - 1] = Suf(firstHead.start + start, ndoc);
                }
             }
             else{
                std::cerr << "it was the first char\n";
             }
          }
       }
    }
    MSGSA[prefSumBucketLengths[_ISA[secondHead.pos]] + (bucketLengths[_ISA[secondHead.pos]]--) - 1] = Suf(secondHead.start, ndoc);
    if(verbose) for(size_t x = 0; x < _sn; x++) {
       if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
       if(verbose) std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
    }

    //put $ instead of X, otherwise the X characters does not lead to a correct comparison (because they are greater)
    for(size_t i = 0; i < _sn; i++) {if(_sx[i] == '%' || _sx[i] == 'X') _sx[i] = '$';}

    //sort S*-suffixes
    uint32_t errStar = 0;
    std::cerr << "Starting to sort S*-suffixes\n";
    std::vector<Suf>::iterator beg = MSGSA.begin();
    for(size_t i = 1; i < _n + 1; i++){
       if(verbose) std::cerr << i << " " << prefSumBucketLengths[i-1] + bucketLengths[i-1] << " " << prefSumBucketLengths[i] << "\n";
       std::sort(beg + prefSumBucketLengths[i-1] + bucketLengths[i-1], beg + prefSumBucketLengths[i], compareSuf);
       /*for(size_t u = prefSumBucketLengths[i-1] + bucketLengths[i-1] + 1; u < prefSumBucketLengths[i]; u++){
         data_type *_slice_sx = _sx + MSGSA[u].idx + docBoundaries[MSGSA[u].doc - 1];
         data_type *_slice_prev = _sx + MSGSA[u-1].idx + docBoundaries[MSGSA[u-1].doc - 1];;
         while(*_slice_sx && *_slice_prev){
          //if(verbose) std::cerr << "suf_i " << *_slice_sx << "\n";
          //if(verbose) std::cerr << "suf_i-1 " << *_slice_prev << "\n";
          if(*_slice_sx == '$' | *_slice_prev == '$'){break;}
          if(*_slice_sx != *_slice_prev){
             if(*_slice_sx < *_slice_prev){
               std::cerr << "PROBLEM with " << u-1 << " (" << MSGSA[u-1].idx << "," << MSGSA[u-1].doc << ")->" << MSGSA[u-1].idx + docBoundaries[MSGSA[u-1].doc - 1] << " and " << u << " (" << MSGSA[u].idx << "," << MSGSA[u].doc << ")->" << MSGSA[u].idx + docBoundaries[MSGSA[u].doc - 1] << "\n"; 
               if(verbose) std::cerr << _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1] << "\n";
               if(verbose) std::cerr << _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1] << "\n";
               if(verbose) std::cerr << "\n";
               //std::cerr << _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1];
               //std::cerr << _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1];
               errStar++;
               //if(err == 2){std::cerr << "error=2\n"; exit(1);}
               break;
             }
             else{
                break;
             }
          }
          
          _slice_sx++;
          _slice_prev++;
         }
       } */
    }
    std::cerr << "errStar: " << errStar << "\n";
    //if(verbose) std::cerr << "Last bucket S*-suffixes\n";
    //std::sort(beg + prefSumBucketLengths[_n-1] + bucketLengths[_n-1], beg + _sn, compareSuf);
    if(verbose) for(size_t x = 0; x < _sn; x++) {
       if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
       if(verbose) std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
    }

    //induce whole GSA
    if(verbose) for(uint64_t i = 0; i < _sn; i++){
       std::cerr << _sx[i] << " type: " << typeArray[i] << "\n";
    }

    std::cerr << "Start inducing L-types\n";
    for(uint64_t i = 0; i < _sn; i++){
       if(beg[i].idx != 0){
          if(typeArray[beg[i].idx + docBoundaries[beg[i].doc - 1] - 1] == 1){
             Suf lSuf = Suf(beg[i].idx - 1, beg[i].doc);
             std::vector<Match>::iterator head = getHead(lSuf);
             MSGSA[prefSumBucketLengths[_ISA[head->pos + (lSuf.idx - head->start)]]++] = lSuf;
          }
       }
       //else if((beg + i)->doc){
       //   std::cerr << "Skipped first char of doc\n";
       //}
    }
    std::cerr << "\nAfter inducing L-types\n";
    if(verbose) for(size_t x = 0; x < _sn; x++) {
       if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
       std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
    }
    
    std::cerr << "Start inducing S-types\n";
    for(uint64_t i = _sn - 1; i < _sn; i--){
       if(verbose) std::cerr << "i: " << i << " " << (beg + i)->idx << "," << (beg + i)->doc << "\n";
       if(beg[i].idx != 0){
          if(typeArray[beg[i].idx + docBoundaries[beg[i].doc - 1] - 1] == 0){
             Suf sSuf = Suf(beg[i].idx - 1, beg[i].doc);
             std::vector<Match>::iterator head = getHead(sSuf);
             MSGSA[prefSumBucketLengthsCopy[_ISA[head->pos + (sSuf.idx - head->start)]]--] = sSuf;
          }
       }
       //else if((beg + i)->doc){
       //   std::cerr << "Skipped first char of doc\n";
       //}
    }
    std::cerr << "\nAfter inducing S-types\n";
    if(verbose) for(size_t x = 0; x < _sn; x++) {
       if(MSGSA[x].doc == 0){std::cerr << "EMPTY\n"; continue;}
       std::cerr << MSGSA[x].idx << " " << MSGSA[x].doc << " " << _sx + MSGSA[x].idx + docBoundaries[MSGSA[x].doc - 1];
    }

    t2 = std::chrono::high_resolution_clock::now();
    uint64_t sortTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
    std::cerr << "Sorted in: " << sortTime << " milliseconds\n";

    std::cerr << "Checking GSA\n"; 
    uint32_t err = 0;
    docBoundaries.push_back(_sn);
    for(size_t i = 0; i < _sn; i++){
       //std::cerr << "i=" << i << ": " << MSGSA[i].idx << " " << MSGSA[i].doc << " " << "\n";//MSGSA[i].head <<"\n";
       data_type *_slice_sx = _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1];
       data_type *_slice_prev;
       uint32_t maxIdx;
       if(i > 0){
         _slice_prev = _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1];
         maxIdx = std::min(docBoundaries[MSGSA[i].doc] - (MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1]), docBoundaries[MSGSA[i-1].doc] - (MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1]));
       } 
       else{
          _slice_prev = (data_type *)"$";
          maxIdx = 1;
       }
       if(verbose) std::cerr << "suf_i-1 " << _slice_prev;
       if(verbose) std::cerr << "suf_i " << _slice_sx << "\n";
       
       
       //while((*_slice_sx != '$') & (*_slice_sx == *_slice_prev)){
      //  while(*_slice_sx && *_slice_prev){
      //     //if(verbose) std::cerr << "suf_i " << *_slice_sx << "\n";
      //     //if(verbose) std::cerr << "suf_i-1 " << *_slice_prev << "\n";
      //     if(*_slice_sx == '$' | *_slice_prev == '$'){break;}
      //     if(*_slice_sx != *_slice_prev){
      //        if(*_slice_sx < *_slice_prev){
      //          std::cerr << "PROBLEM with " << i-1 << " (" << MSGSA[i-1].idx << "," << MSGSA[i-1].doc << ")->" << MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1] << " and " << i << " (" << MSGSA[i].idx << "," << MSGSA[i].doc << ")->" << MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1] << "\n"; 
      //          if(verbose) std::cerr << _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1] << "\n";
      //          if(verbose) std::cerr << _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1] << "\n";
      //          if(verbose) std::cerr << "\n";
      //          //std::cerr << _sx + MSGSA[i-1].idx + docBoundaries[MSGSA[i-1].doc - 1];
      //          //std::cerr << _sx + MSGSA[i].idx + docBoundaries[MSGSA[i].doc - 1];
      //          err++;
      //          //if(err == 2){std::cerr << "error=2\n"; exit(1);}
      //          break;
      //        }
      //        else{
      //           break;
      //        }
      //     }
          
      //     _slice_sx++;
      //     _slice_prev++;
      //  }
      //  if(*_slice_sx < *_slice_prev){
      //     err++;
      //  }
      if(memcmp(_slice_sx, _slice_prev, maxIdx) < 0){
         //std::cerr << "PROBLEM with " << i-1 << " (" << MSGSA[i-1].idx << "," << MSGSA[i-1].doc << ") and " << i << " (" << MSGSA[i].idx << "," << MSGSA[i].doc << ")\n"; 
         err++;
         //if(err) break;
      }
    }
    std::cerr << "n. errors " << err << "\n"; 
    std::cerr << "maxCounter " << maxCounter << "\n";
    std::cerr << "meanCounter " << sumCounter/(denCounter+0.00000001) << "\n";
    std::cerr << "times it had to compare only one char " << diffLen << "\n";
    std::cerr << "times it had to compare more than one char " << denCounter << "\n";
    //std::cerr << "n. of ties " << tiesCounter << "\n";
    delete[] sx;
    delete[] bucketLengths;
    delete[] prefSumBucketLengths;
    delete[] prefSumBucketLengthsCopy;
    delete[] _LCP;
    delete[] _ISA;
    delete[] _SA;
    MSGSA.clear();
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
    if(_sx[i] == 'N'){
       //std::cerr << "Hit a run of Ns... \n";
       //std::cerr.flush();
       uint64_t start = i;
       while(_sx[i] == 'N' && _sx[i]  != '$'){ //file should be terminated with an X, so no need to check length ---> && i < _sn){
          i++;
       }
       mismatchingSymbol = _sx[i];
       *len = i - start;
       *pos = _n;
       //std::cerr << "Hit a run of Ns, " << *len << " symbols long.\n";
       return;
    }
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
            if(verbose) std::cout << "nlb after binary search " << nlb << "\n";
            //std::cerr << "nlb: " << nlb << "\n";
            if (nlb < 0) {
                //no match, the game is up
                //fprintf(stderr,"Breaking from 2; offset = %lu; _sx[%lu] = %u\n",offset,j,_sx[j]);
                maxMatch = -(nlb)-1;
                if(verbose) std::cout << "nlb was negative " << maxMatch << "\n";
                if(verbose) std::cout << "nrb is " << nrb << "\n";
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

