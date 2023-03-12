import DirNode from "../directory";
import { getFileFromPath, mntHierarchyNested } from "../../utils";

describe('FileTypes class tests', () => {
  describe('DirNode class', () => {
    let dirClass: DirNode;
    beforeAll(() => {
      dirClass = new DirNode(mntHierarchyNested);
    })
    it('toObject successfully converts class to JSONable object', () => {
      expect(dirClass.toString()).toContain('Start Menu');
    });
    it('isReadOnly cascades', () => {
      const myFolder = getFileFromPath('/mnt/c/usr/me', dirClass);
      expect(myFolder?.isReadOnly()).toEqual(false);
      dirClass.readonly = true;
      expect(myFolder?.isReadOnly()).toEqual(true);
    });
  });
});
