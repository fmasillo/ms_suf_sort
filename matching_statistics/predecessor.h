#ifndef __PREDECESSOR_H
#define __PREDECESSOR_H

#include <algorithm>
#include <vector>
#include <stdint.h>
#include <cmath>
#include <bitset>
#include "match.h"

struct predEle{
	uint32_t value;
	uint32_t startIndex;
	predEle(){}
	predEle(uint32_t v, uint32_t s){
		value = v; startIndex = s;
	}
};

struct predecessor{
	std::vector<predEle *> sampledPredArray;
	std::vector<uint32_t> docSizes;
	uint32_t nDocs;
	predecessor(){}
	predecessor(std::vector<Match> phrases, std::vector<uint32_t> headBoundaries, uint64_t numDocs){
		auto t1 = std::chrono::high_resolution_clock::now();
		nDocs = numDocs;
		sampledPredArray.resize(numDocs);
		uint32_t sampleRate = 10;
		uint32_t *nHeadsSampled = new uint32_t[numDocs];
		uint32_t size;
		for(uint32_t i = 1; i < nDocs; i++){
			nHeadsSampled[i] = headBoundaries[i] - headBoundaries[i-1];
			//std::cerr << "nHeads for doc_" << i << ": " << nHeadsSampled[i] << "\n";
			size = ceil((float)nHeadsSampled[i]/sampleRate);
			sampledPredArray[i-1] = new predEle[size];
			docSizes.push_back(size);
		}
		uint32_t currentDoc = 0;
		uint32_t pos = 0;
		uint32_t x = 0;
		for(uint32_t i = 0; i < phrases.size(); i++){
			if(i == headBoundaries[currentDoc]){
				currentDoc++;
				pos = 0;
				x = 0;
			}
			if(pos++ % sampleRate == 0){
				sampledPredArray[currentDoc-1][x++] = predEle(phrases[i].start, i);
				//std::cerr << "doc_" << currentDoc-1 << ": " << sampledPredArray[currentDoc-1][x-1].value << "," << sampledPredArray[currentDoc-1][x-1].startIndex << "\n";
			}
		}
		auto t2 = std::chrono::high_resolution_clock::now();
		uint64_t constructionTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
		std::cerr << "Finished building predecessor data structure in " << constructionTime << " milliseconds\n";
	}

	inline std::vector<Match>::iterator predQuery(const Match query, std::vector<Match> &phrases){
		predEle *pred = std::upper_bound(sampledPredArray[query.len-1], sampledPredArray[query.len-1]+docSizes[query.len-1], predEle(query.start, 0), 
			[](const predEle first, const predEle second){return first.value < second.value;}
		) - 1;
		uint32_t startIdx = pred->startIndex;
		while(startIdx < phrases.size() && phrases[startIdx].start <= query.start){
			startIdx++;
			if(phrases[startIdx].start == 0) break;
		}
		return phrases.begin() + startIdx-1;
	}

	inline Match predQuery(const Suf query, const std::vector<Match> &phrases){
		//std::cerr << "before binary search\n";
		predEle *pred = std::upper_bound(sampledPredArray[query.doc-1], 
			sampledPredArray[query.doc-1]+docSizes[query.doc-1], predEle(query.idx, 0), 
			[](const predEle first, const predEle second){return first.value < second.value;}
		) - 1;
		//std::cerr << "after binary search\n";
		uint32_t startIdx = pred->startIndex;
		//std::cerr << "startIdx " << startIdx << "\n";
		//std::cerr << "before scan\n";
		while(startIdx < phrases.size() && phrases[startIdx].start <= query.idx){
			startIdx++;
			if(phrases[startIdx].start == 0) break;
		}
		//std::cerr << "after scan " << startIdx << "\n";
		return phrases[startIdx-1];
	}
};

struct  predEle2{
	uint32_t start;
	uint32_t end;
	predEle2(){
		start = 0; end = 0;
	}
	predEle2(uint32_t s, uint32_t e){
		start = s; end = e;
	}
};

static const int32_t nOfDigits[] =
        {
            1 << 8, 1 << 9, 1 << 10, 1 << 11, 
			1 << 12, 1 << 13, 1 << 14, 1 << 15,
			1 << 16, 1 << 17, 1 << 18, 1 << 19,
			1 << 20, 1 << 21, 1 << 22, 1 << 23,
			1 << 24, 1 << 25, 1 << 26, 1 << 27,
			1 << 28, 1 << 29, 1 << 30, 1 << 31    
        };

struct predecessor2{
	std::vector<predEle2 *> sampledPredArray;
	std::vector<uint32_t> docSizes;
	uint32_t nDocs;
	uint32_t mask;
	uint8_t shift;
	predecessor2(){}
	predecessor2(std::vector<Match> phrases, std::vector<uint32_t> headBoundaries, uint64_t numDocs, uint32_t maxValue){
		auto t1 = std::chrono::high_resolution_clock::now();
		nDocs = numDocs;
		sampledPredArray.resize(numDocs);
		//uint32_t *nHeadsSampled = new uint32_t[numDocs];
		docSizes.push_back(0);
		for(uint32_t i = 1; i < nDocs; i++){
			//nHeadsSampled[i] = headBoundaries[i] - headBoundaries[i-1];
			//std::cerr << "nHeads for doc_" << i << ": " << nHeadsSampled[i] << "\n";
			sampledPredArray[i-1] = new predEle2[256]();
			docSizes.push_back(headBoundaries[i]);
		}
		uint32_t max = maxValue;
		std::bitset<32> m(max);
		std::cerr << maxValue << " " << m << "\n";
		for(uint8_t i = 0; i < 24; i++){
			if(maxValue < nOfDigits[i]){
				shift = i;
				mask = (nOfDigits[0]-1) << shift;
				std::bitset<32> y(mask);
				std::cerr << y << "\n";
				break;
			}
		} 
		uint32_t currentDoc = 0;
		for(uint32_t i = 0; i < phrases.size(); i++){
			if(i == headBoundaries[currentDoc]){
				currentDoc++;
			}
			uint8_t key = (phrases[i].start & mask) >> shift;
			sampledPredArray[currentDoc-1][key].end++;
		}
		for(uint32_t doc = 0; doc < numDocs-1; doc++){
			for(uint16_t i = 1; i < 256; i++){
				if(sampledPredArray[doc][i].end == 0){
					sampledPredArray[doc][i].start = sampledPredArray[doc][i-1].start;
					sampledPredArray[doc][i].end = sampledPredArray[doc][i-1].end;
				}
				else{
					sampledPredArray[doc][i].start = sampledPredArray[doc][i-1].end;
					sampledPredArray[doc][i].end = sampledPredArray[doc][i].end + sampledPredArray[doc][i].start;
				}
				//std::cerr << sampledPredArray[doc][i].end - sampledPredArray[doc][i].start << "\n";
			}
		}
		auto t2 = std::chrono::high_resolution_clock::now();
		uint64_t constructionTime = std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
		std::cerr << "Finished building predecessor data structure in " << constructionTime << " milliseconds\n";
	}

	inline std::vector<Match>::iterator predQuery2(const Match query, std::vector<Match> &phrases){
		//uint8_t key = (query.start & mask) >> shift;
		uint8_t key = query.start >> shift;
		std::vector<Match>::iterator beg = phrases.begin();
		// if(sampledPredArray[query.len-1][key].end - sampledPredArray[query.len-1][key].start < 30){
		// 	std::vector<Match>::iterator it;
		// 	for(it = beg + sampledPredArray[query.len-1][key].start + docSizes[query.len-1]; it < beg + sampledPredArray[query.len-1][key].end + docSizes[query.len-1]; it++){
		// 		if(it->start > query.start) return it-1;
		// 	}
		// 	return it-1;
		// }
		// else{
			return std::upper_bound(beg + sampledPredArray[query.len-1][key].start + docSizes[query.len-1], 
			beg + sampledPredArray[query.len-1][key].end + docSizes[query.len-1], Match(query.start, 0, 0), 
			[](const Match first, const Match second){return first.start < second.start;}
			) - 1;
		// }
	}

	inline Match predQuery2(const Suf query, std::vector<Match> &phrases){
		//uint8_t key = (query.idx & mask) >> shift;
		uint8_t key = query.idx >> shift;
		std::vector<Match>::iterator beg = phrases.begin();
		// if(sampledPredArray[query.doc-1][key].end - sampledPredArray[query.doc-1][key].start < 30){
		// 	std::vector<Match>::iterator it;
		// 	for(it = beg + sampledPredArray[query.doc-1][key].start + docSizes[query.doc-1]; it < beg + sampledPredArray[query.doc-1][key].end + docSizes[query.doc-1]; it++){
		// 		if(it->start > query.idx) return *(it-1);
		// 	}
		// 	return *(it-1);
		// }
		// else{
			return *(std::upper_bound(beg + sampledPredArray[query.doc-1][key].start + docSizes[query.doc-1], 
			beg + sampledPredArray[query.doc-1][key].end + docSizes[query.doc-1], Match(query.idx, 0, 0), 
			[](const Match first, const Match second){return first.start < second.start;}
			) - 1);
		// }
	}
};

#endif // __RMQ_TREE_H
