#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "openssl/sha.h"
#include "sha256-util.h"


void sha256_hash_string(unsigned char hash[SHA256_DIGEST_LENGTH], unsigned char outputBuffer[65]);

void sha256_bytes(unsigned char *pData, int len, unsigned char hash[SHA256_DIGEST_LENGTH])
{
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    SHA256_Update(&sha256, pData, len);
    SHA256_Final(hash, &sha256);
}

void sha256_string(unsigned char *pData, int len, unsigned char outputBuffer[65])
{
    unsigned char hash[SHA256_DIGEST_LENGTH];
    sha256_bytes(pData, len, hash);
    int i = 0;
    for(i = 0; i < SHA256_DIGEST_LENGTH; i++) {
        sprintf((char *)outputBuffer + (i * 2), "%02x", hash[i]);
    }
    outputBuffer[64] = 0;
}

void sha256_hash_string(unsigned char hash[SHA256_DIGEST_LENGTH], unsigned char outputBuffer[65])
{
    int i = 0;

    for(i = 0; i < SHA256_DIGEST_LENGTH; i++){
        sprintf((char *)outputBuffer + (i * 2), "%02x", hash[i]);
    }
    outputBuffer[64] = 0;
}

int sha256_file(const char *path, unsigned char outputBuffer[65])
{
    FILE *file = fopen(path, "rb");
    if(!file) return -534;

    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    const int bufSize = 32768;
    unsigned char *buffer = (unsigned char *)malloc(bufSize);
    int bytesRead = 0;
    if(!buffer) return -1;
    while((bytesRead = fread(buffer, 1, bufSize, file))) {
        SHA256_Update(&sha256, buffer, bytesRead);
    }
    SHA256_Final(hash, &sha256);

    sha256_hash_string(hash, (unsigned char *)outputBuffer);
    fclose(file);
    free(buffer);
    return 0;
}

int getRandomOffsets(
		const char *ARG_VIDEO_PATH1,
		const char *ARG_VIDEO_PATH2,
		int *frameOffset,
		int frame_range,
		int *mbOffset,
		int mb_range
		)
{
	unsigned char hashSrc[65];
	unsigned char hashTrans[65];
	sha256_file(ARG_VIDEO_PATH1, hashSrc);
	printf("hashSrc=%s\n", hashSrc);
	sha256_file(ARG_VIDEO_PATH2, hashTrans);
	printf("hashTrans=%s\n", hashTrans);

	int frame0 = strtol((const char *)hashSrc+62, NULL, 16); // Last two bytes
	int frame1 = strtol((const char *)hashTrans+62, NULL, 16); // Last two bytes
	*frameOffset = (frame0 + frame1) % frame_range;

	int mb0 = strtol((const char *)hashSrc+60, NULL, 16); // Last 4 bytes
	int mb1 = strtol((const char *)hashTrans+60, NULL, 16); // Last 4 bytes
	*mbOffset =  (mb0 + mb1) % mb_range;

	return 0;
}

