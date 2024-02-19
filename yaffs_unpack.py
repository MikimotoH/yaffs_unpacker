#!/usr/bin/env python3

import cstruct
import ctypes
from enum import IntEnum, Enum
import itertools 
import argparse
from pathlib import Path
from typing import Dict, Iterator, BinaryIO, TypedDict
import time
import os
import re
import io
import errno
import shutil
import sys
import logging
from datetime import datetime
import struct

logger = logging.getLogger(__name__)

class yaffs_obj_type(IntEnum):
	YAFFS_OBJECT_TYPE_UNKNOWN=0
	YAFFS_OBJECT_TYPE_FILE=1
	YAFFS_OBJECT_TYPE_SYMLINK=2
	YAFFS_OBJECT_TYPE_DIRECTORY=3
	YAFFS_OBJECT_TYPE_HARDLINK=4
	YAFFS_OBJECT_TYPE_SPECIAL=5
     
class yaffs_obj_type(cstruct.CEnum):
    __size__ = 4
    __def__ = """
        enum  {
            YAFFS_OBJECT_TYPE_UNKNOWN = 0,
            YAFFS_OBJECT_TYPE_FILE,
            YAFFS_OBJECT_TYPE_SYMLINK,
            YAFFS_OBJECT_TYPE_DIRECTORY,
            YAFFS_OBJECT_TYPE_HARDLINK,
            YAFFS_OBJECT_TYPE_SPECIAL
        } 
    """

cstruct.typedef("uint8", "u8")
cstruct.typedef("uint16", "u16")
cstruct.typedef("uint32", "u32")
cstruct.typedef("uint32", "u32_time_t")
cstruct.typedef("int16", "sint16")
cstruct.typedef("uint32", "u32_file_mode")
cstruct.typedef("int32", "s32")

class ObjHdr:
    def __init__(self) -> None:
        self.type = yaffs_obj_type.YAFFS_OBJECT_TYPE_UNKNOWN
        self.parent_obj_id = -1
        self.name = ""
        self.file_mode = 0o000000
        self.uid = -1
        self.gid = -1
        self.atime = 0 # Epoch seconds from Jan 1 1970
        self.mtime = 0 # Epoch seconds from Jan 1 1970
        self.ctime = 0 # Epoch seconds from Jan 1 1970
        self.file_size = -1
        self.alias = "" # symbolic-link target

        
def c_null_term_str_to_str(data:bytes) -> str:
    if all(_ == 0xFF for _ in data):
        return ""
    return data.split(b'\x00')[0].decode('utf8')


class yaffs_obj_hdr(cstruct.CStruct):
    __byte_order__ = cstruct.LITTLE_ENDIAN
    __def__ = """
    struct {
        enum yaffs_obj_type type;
        u32 parent_obj_id;
        u16 always_0xFFFF;
        char name[255];
        u8   always_0xFF;
        u16  always_0xFFFF_2;
        u32_file_mode yst_mode;
        u32 yst_uid;
        u32 yst_gid;
        u32_time_t yst_atime;
        u32_time_t yst_mtime;
        u32_time_t yst_ctime;
        u32 file_size_low;
        s32 equiv_id;
        char alias[160];
        u32 yst_rdev;
        u32 win_ctime[2];
        u32 win_atime[2];
        u32 win_mtime[2];
        u32 inband_shadowed_obj_id;
        u32 inband_is_shrink;
        u32 file_size_high;
        u32 reserved[1];
        s32 shadows_obj;
        u32 is_shrink;
    }
    """
    
    def get_ObjHdr(self, data: bytes) -> ObjHdr:
        cstruct.CStruct.unpack(self, data)
        oh = ObjHdr()
        oh.type = self.type
        oh.parent_obj_id = self.parent_obj_id
        oh.name = c_null_term_str_to_str(self.name)
        oh.file_mode = self.yst_mode
        oh.uid = self.yst_uid
        oh.gid = self.yst_gid
        oh.atime = self.yst_atime
        oh.mtime = self.yst_mtime
        oh.ctime = self.yst_ctime
        if oh.type == yaffs_obj_type.YAFFS_OBJECT_TYPE_FILE:
            if self.file_size_high != 0xFFFFFFFF:
                oh.file_size = self.file_size_low | self.file_size_high<<32
            else:
                oh.file_size = self.file_size_low
        else:
            oh.file_size = -1
        oh.alias = c_null_term_str_to_str(self.alias)
        return oh

     
class yaffs_magic_header(cstruct.CStruct):
    __byte_order__ = cstruct.LITTLE_ENDIAN
    __def__ = """
    struct {
        u32 type;
        u32 parent_obj_id;
        u16 always_0xFFFF;        
    }    
    """
    def is_valid(self)->bool:
        return (self.type in [1,2,3,4,5] and \
                self.always_0xFFFF   == 0xFFFF and \
                self.always_0xFF     ==   0xFF and \
                self.always_0xFFFF_2 == 0xFFFF)

        
    

class yaffs_packed_tags2(cstruct.CStruct):
    __byte_order__ = cstruct.LITTLE_ENDIAN
    __def__ = """
    struct {
        u32 seq_number; 
        u32 obj_id;
        u32 chunk_id;
        u32 n_bytes;
        u8 col_parity;
        u8 __nouse__[3];
        u32 line_parity;
        u32 line_parity_prime;
    };
    """ 

class CorruptedType(Exception):
    pass

class CorruptedPage(Exception):
    pass

class WrongPageSize(Exception):
    pass

class WrongPageData(Exception):
    pass

class WrongYaffsObjType(Exception):
    def __init__(self, *args: object) -> None:
        super().__init__(*args)
        self.yaffs_type = args[0]

def detect_endianness(ymh: yaffs_magic_header) -> str:
    """_summary_

    :param fin: file object this is opened by `io.open(file_path, 'rb')`
    :return: cstruct.LITTLE_ENDIAN, or cstruct.BIG_ENDIAN 
    """
    if ymh.type in [0x1, 0x2, 0x3, 0x4, 0x5]:
        return cstruct.LITTLE_ENDIAN
    elif ymh.type in [0x1 <<24, 0x2<<24, 0x3<<24, 0x4<<24, 0x4<<24, 0x5<<24]:
        return cstruct.BIG_ENDIAN
    else:
        raise CorruptedType()
    
def set_endianness(endianness):
    global yaffs_obj_hdr, yaffs_magic_header

    yaffs_obj_hdr = yaffs_obj_hdr.parse(
        yaffs_obj_hdr.__def__,
        __name__=yaffs_obj_hdr.__name__,
        __byte_order__=endianness,
    )
    yaffs_magic_header = yaffs_magic_header.parse(
        yaffs_magic_header.__def__,
        __name__=yaffs_magic_header.__name__,
        __byte_order__=endianness,
    )

def is_valid_yaffs_magic_header(ymh: yaffs_magic_header)->bool:
    return ymh.type in [1,2,3,4,5] and ymh.sum_no_longer_used==0xFFFF

class YAFFS_unpacker:
    def __init__(self):
        self.objdict = dict()
        # take Official YAFFS1 param as default
        self.yaffs_version = 1
        self.endianness = cstruct.LITTLE_ENDIAN
        self.page_size = 512
        self.spare_size = self.page_size//32
    
    def _unwind_parent_name(self, obj_id:int) -> Iterator[str]:
        while obj_id in self.objdict:
            yield self.objdict[obj_id].name
            obj_id = self.objdict[obj_id].parent_obj_id

    def _test_page_size(self, fin:BinaryIO, page_size:int):
        fin.seek(0, io.SEEK_SET)
        data = fin.read(page_size)
        if not all(_==0xFF for _ in data[yaffs_obj_hdr.size:]):
            return False
        return True
    
    def _detect_param(self, fin:BinaryIO):
        logger.debug("_detect_param enter")
        fin.seek(0, io.SEEK_SET)
        ymh = yaffs_magic_header()
        ymh.unpack(fin.read(ymh.size))
        self.endianness = detect_endianness(ymh)
        logger.info("self.endianness =\"%s\"", self.endianness)
        set_endianness(self.endianness)
        
        fin.seek(0, io.SEEK_SET)
        yoh = yaffs_obj_hdr()
        obj_hdr = yoh.get_ObjHdr(fin.read(yoh.size))
        if not obj_hdr.name and not obj_hdr.alias:
            self.yaffs_version = 1 
            self.page_size = 512
            self.spare_size = self.page_size// 32
            return
            
        self.yaffs_version = 2 
        allowed_page_size = [16384, 8192, 4096, 2048, 512, ]
        self.page_size = -1
        for page_size in allowed_page_size:
            if self._test_page_size(fin, page_size):
                self.page_size = page_size
                break
        if self.page_size == -1:
            raise WrongPageSize()
        self.spare_size = self.page_size // 32 
        fin.seek(0, io.SEEK_SET)        

        
    def unpack(self, imgFile:Path, outdir:Path):
        """ unpack YAFFS image file into output directory

        :param Path imgFile: input YAFFS1 image file
        :param outdir: output directory
        """
        with imgFile.open('rb') as fin:
            self._detect_param(fin)
            logger.info("self.yaffs_version=%s, self.page_size=%s", self.yaffs_version, self.page_size)
            if self.yaffs_version == 1:
                fin.seek(self.page_size + self.spare_size, io.SEEK_SET)
            else:
                fin.seek(0)
            yoh = yaffs_obj_hdr()
            for obj_id in itertools.count(256+1):
                try:
                    data = fin.read(self.page_size)
                    obj_hdr = yoh.get_ObjHdr(data[:yoh.size])
                except (struct.error, ValueError) as ex:
                    break
                fin.read(self.spare_size)
                self.objdict[obj_id] = obj_hdr
                obj_path = list(reversed(list(self._unwind_parent_name(obj_id))))
                obj_path = os.sep.join([str(outdir)] + obj_path)
                obj_path = Path(obj_path).absolute()
                logger.info(f"{obj_path=}, {obj_id=} {obj_hdr.type=}, {obj_hdr.alias=}")
                if obj_hdr.type == yaffs_obj_type.YAFFS_OBJECT_TYPE_DIRECTORY:
                    os.mkdir(obj_path)
                elif obj_hdr.type == yaffs_obj_type.YAFFS_OBJECT_TYPE_FILE:
                    num_pages = (obj_hdr.file_size + self.page_size -1) // self.page_size
                    logger.info("write obj_path=%s, file_size=%s bytes", obj_path, obj_hdr.file_size) 
                    with Path(obj_path).open('wb') as fout:
                        for i_page in range(num_pages):
                            page_data = fin.read(self.page_size)
                            if i_page < num_pages-1:
                                fout.write(page_data)
                            else:
                                fout.write(page_data[:obj_hdr.file_size%self.page_size])
                            fin.seek(self.spare_size, io.SEEK_CUR)     
                elif obj_hdr.type == yaffs_obj_type.YAFFS_OBJECT_TYPE_SYMLINK:
                    os.symlink(obj_hdr.alias, obj_path)
                else:
                    logger.warning("Wrong obj_hdr.type = %d", obj_hdr.type)
                    raise WrongYaffsObjType(obj_hdr.type)
                os.utime(obj_path, (obj_hdr.atime, obj_hdr.mtime), follow_symlinks=False)
                    

def detect_yaffs(imgFilePath:Path)->bool:
    with imgFilePath.open('rb') as fin:
        data = fin.read(4+4+2)
        yaffs_le = br'[\x01-\x05]\x00{3}\x01\x00{3}\xFF{2}'
        yaffs_be = br'\x00{3}[\x01-\x05]\x00{3}\x01\xFF{2}'
        if re.match(yaffs_le, data):
            return True
        elif re.match(yaffs_be, data):
            return True
        else:
            return False
    
            
def main():    
    parser = argparse.ArgumentParser()
    parser.add_argument("imgFile")
    parser.add_argument("outdir")
    args = parser.parse_args()
    unpacker = YAFFS_unpacker()
    imgFilePath = Path(args.imgFile).absolute()
    if not detect_yaffs(imgFilePath):
        sys.stdout.write(f'{imgFilePath=} is not a valid YAFFS file\n')
        return errno.EINVAL 
    outdir = Path(args.outdir).absolute()
    if outdir.exists() and outdir.is_dir():
        shutil.rmtree(outdir)
    os.mkdir(outdir)
    unpacker.unpack(imgFilePath, outdir)
    return 0
    

if __name__=='__main__':
    logging.basicConfig(
        format="%(asctime)s %(name)s [%(filename)s:%(lineno)s - %(funcName)s] %(levelname)s %(message)s",
        stream=sys.stdout, level=logging.DEBUG)
    main()