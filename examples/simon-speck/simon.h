#ifndef TOOLS_H
#define TOOLS_H

#define ROTATE_LEFT_8(x,n) ( ((x) << (n)) | ((x) >> (8-(n))) )
#define ROTATE_LEFT_16(x,n) ( ((x) << (n)) | ((x) >> (16-(n))) )
#define ROTATE_LEFT_32(x,n) ( ((x) << (n)) | ((x) >> (32-(n))) )
#define ROTATE_LEFT_64(x,n) ( ((x) << (n)) | ((x) >> (64-(n))) )

#define ROTATE_RIGHT_8(x,n) ( ((x) >> (n)) | ((x) << (8-(n))) )
#define ROTATE_RIGHT_16(x,n) ( ((x) >> (n)) | ((x) << (16-(n))) )
#define ROTATE_RIGHT_32(x,n) ( ((x) >> (n)) | ((x) << (32-(n))) )
#define ROTATE_RIGHT_64(x,n) ( ((x) >> (n)) | ((x) << (64-(n))) )

#endif

