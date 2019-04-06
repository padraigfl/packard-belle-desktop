import React, { Component } from "react";
import { SettingsContext } from "../../contexts/settings";
import { ProgramContext } from "../../contexts/programs";
import {
  Window as AbstractWindow,
  DetailsSection,
  Checkbox,
  Radio
} from "packard-belle";
import Window from "../tools/Window";

import { buildMenu } from "../ExplorerWindow/ExplorerWindow";

class Settings extends Component {
  static contextType = SettingsContext;
  state = {
    selected: null
  };

  onSelect = selected => this.setState({ selected });

  exit = () => {
    if (this.state.selected) {
      this.context.onClose(this.state.selected, true);
    }
  };

  moveToTop = () => {
    if (this.state.selected) {
      this.context.moveToTop(this.state.selected);
    }
  };

  tempChange = (func, revertFunc) => {
    func();
    this.setState(state => ({ tempChange: true }));
    setTimeout(() => {
      this.setState(state => ({ tempChange: false }));
      revertFunc();
    }, 5000);
  };

  render() {
    const { context, props } = this;
    return (
      <ProgramContext.Consumer>
        {program =>
          program.settingsDisplay && (
            <Window
              {...props}
              resizable={false}
              initialX={200}
              initialY={150}
              initialWidth={240}
            >
              {rnd => (
                <AbstractWindow
                  title="Task Manager"
                  className="Settings"
                  onHelp={() => {}} // @todo
                  onClose={() => program.toggleSettings(false)}
                  changingState={rnd.state.isDragging}
                  resizable={false}
                  menuOptions={buildMenu({
                    ...props,
                    onClose: program.toggleSettings
                  })}
                >
                  <DetailsSection title="customise">
                    <Checkbox
                      id="Mobile View"
                      label="Mobile View"
                      onChange={context.toggleMobile}
                      checked={context.isMobile === true}
                    />
                    <Checkbox
                      id="CRT Effect"
                      label="CRT Effect"
                      onChange={context.toggleCrt}
                      checked={context.crt === true}
                    />
                    <Checkbox
                      id="Fullscreen"
                      label="Fullscreen"
                      onChange={context.toggleCrt}
                      checked={context.crt === true}
                    />
                  </DetailsSection>
                  <DetailsSection title="Scale Options">
                    <div className="options-row">
                      {[1, 1.5, 2].map(scale => (
                        <Radio
                          id={scale}
                          label={`${scale * 100}%`}
                          value={scale}
                          onChange={e => {
                            this.tempChange(
                              () => context.changeScale(+e.target.value),
                              () => context.changeScale(context.scale)
                            );
                          }}
                          checked={context.scale === scale}
                        />
                      ))}
                    </div>
                  </DetailsSection>
                  {this.state.tempChange && "Previewing Changes"}
                </AbstractWindow>
              )}
            </Window>
          )
        }
      </ProgramContext.Consumer>
    );
  }
}

export default Settings;
