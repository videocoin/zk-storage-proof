
#ifndef EXTOOLS_SHA256_UTIL_H_
#define EXTOOLS_SHA256_UTIL_H_


void sha256_string(unsigned char *pData, int len, unsigned char outputBuffer[65]);
int sha256_file(const char *path, unsigned char outputBuffer[65]);
void sha256_bytes(unsigned char *pData, int len, unsigned char hash[32]);

int getRandomOffsets(
		const char *ARG_VIDEO_PATH1,
		const char *ARG_VIDEO_PATH2,
		int *frameOffset,
		int frame_range,
		int *mbOffset,
		int mb_range
		);
#endif /* EXTOOLS_SHA256_UTIL_H_ */
