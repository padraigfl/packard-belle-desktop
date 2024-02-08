import React, { Component } from "react";
import * as Applications from "../Applications";
import { ProgramContext } from "../../contexts";

class WindowManager extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <>
        {Object.keys(this.context.activePrograms)
          // .filter(prog => !prog.minimized)
          .map(progId => {
            const prog = this.context.activePrograms[progId]
            const Application = Applications[prog.component];
            return (
              <Application
                {...prog}
                save={this.context.save}
                key={progId}
                onClose={this.context.onClose}
                onOpen={this.context.onOpen}
                onMinimize={this.context.onMinimize}
                moveToTop={this.context.moveToTop}
                isActive={prog.id === this.context.activeId}
                program={prog}
                zIndex={this.context.zIndexes.indexOf(progId) + 5}
              />
            );
          })}
      </>
    );
  }
}

export default WindowManager;
