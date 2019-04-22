import React, { Component } from "react";
import * as Applications from "../Applications";
import { ProgramContext } from "../../contexts";

class WindowManager extends Component {
  static contextType = ProgramContext;

  render() {
    return (
      <>
        {this.context.activePrograms
          .filter(prog => !prog.minimized)
          .map(prog => {
            const Application = Applications[prog.component];
            return (
              <Application
                {...prog}
                save={this.context.save}
                key={prog.id || prog.key}
                onClose={this.context.onClose}
                onOpen={this.context.onOpen}
                onMinimize={this.context.onMinimize}
                moveToTop={this.context.moveToTop}
                isActive={prog.id === this.context.activeId}
                program={prog}
              />
            );
          })}
      </>
    );
  }
}

export default WindowManager;
