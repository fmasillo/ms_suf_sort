#ifndef __MATCH_H
#define __MATCH_H
#include <stdint.h>

struct Match{
   //uint64_t suf; //position of suffix in collection
   uint32_t start; //position in the collection 
   uint32_t pos; //position of match in _reference
   uint32_t len; //length of match
   //data_type next; //symbol in the collection after the match
   bool smaller;
   Match(){}
   //Match(uint32_t p, uint32_t l, unsigned char nxt){
   //   pos = p; len = l, next = nxt;
   //}
   Match(uint32_t s, uint32_t p, uint32_t l){
      start = s; pos = p; len = l; 
   }
   Match(uint32_t s, uint32_t p, uint32_t l, bool sm){
      start = s; pos = p; len = l; smaller = sm;
   }
   void changeS(uint32_t s){
      start = s;
   }
   void changeP(uint32_t p){
      pos = p;
   }
   void changeD(uint32_t d){
      len = d;
   }
};

struct SufSStar{
   uint32_t idx;
   uint32_t doc;
   uint32_t head;
   SufSStar(){idx = 0; doc = 0; head = 0;}
   SufSStar(uint32_t i, uint32_t d, uint32_t h){
      idx = i; doc = d; head = h;
   }
};

struct Suf{
   uint32_t idx;
   uint32_t doc;
   Suf(){idx = 0; doc = 0;}
   Suf(uint32_t i, uint32_t d){
      idx = i; doc = d;
   }
   Suf(SufSStar &s){
      idx = s.idx; doc = s.doc;
   }
   // void changeDocSign(){
   //    doc = ~doc;
   // }
};

#endif