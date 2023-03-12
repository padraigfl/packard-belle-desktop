import { AbstractFileParams } from "../classes/abstract";
import DirNode from "../classes/directory";
import { ValidFileNode } from "../classes/types";
import { mntHierarchyNested, getFileFromPath, deleteFile } from "../utils";

describe('filesystem utils', () => {
  let fileSystem: any;
  describe('cross referencing filesystem class and object interoperability', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('class and object have same keys and values', () => {
      const checkAllChildrenForDifference = (object: AbstractFileParams, chain: string[]): boolean => {
        let acc = false;
        const filePath = [...chain, object.name];
        const matchingFile = getFileFromPath(`${filePath.join('/')}` || '/', fileSystem);
        Object.entries(object).forEach(([k, v]) => {
          if (['name', 'link'].includes(k) && v !== (matchingFile as any)[k]) {
            acc = true;
          }
          if (k === 'data') {
            acc = Object.entries(v).some(([k, v]) => typeof v !== 'object' && v === (matchingFile as any).data[k]);
          }
          if (k === 'contents' && !acc) {
            acc = v.some((_: ValidFileNode) => checkAllChildrenForDifference(_, [...filePath]))
          }
        });
        return acc;
      }
      expect(checkAllChildrenForDifference(mntHierarchyNested, [])).toBeFalsy();
    });
  });
  describe('getFileFromPath', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('can get root', () => {
      expect(getFileFromPath('', fileSystem)).toBeTruthy();
    });
    it('absolute path applied to root', () => {
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', fileSystem)).toBeTruthy();
    });
    it('get from relative path (i.e. "search current directory"', () => {
      expect(getFileFromPath('usr/me/desktop/resume.txt', getFileFromPath('mnt/c', fileSystem) as DirNode)).toBeTruthy();
    });
    it('get from absolute path applied to nested path (i.e. "search everywhere")', () => {
      const cDrive = getFileFromPath('mnt/c', fileSystem) as DirNode;
      expect(getFileFromPath('/mnt/c/usr/me/desktop/resume.txt', cDrive)).toBeTruthy();
    });
  });
  describe('deleteFile', () => {
    beforeAll(() => {
      fileSystem = new DirNode(mntHierarchyNested, null);
    })
    it('deletes selected file', () => {
      const path = '/mnt/c/usr/me/desktop/readme.html';
      deleteFile(fileSystem, path);
      expect(getFileFromPath(path, fileSystem)).toBeFalsy();
    });
    it('error if attempt root delete', () => {
      const path = '/';
      try {
        deleteFile(fileSystem, path);
      } catch(e: any) {
        expect(e?.message).toEqual('unauthorized');
      }
    });
    it('error if no file', () => {
      const path = '/mnt/c/usr/me/desktop/not-an-actual-file.html';
      try {
        deleteFile(fileSystem, path);
      } catch(e: any) {
        expect(e?.message).toEqual('no-such-file');
      }
    });
  });
});